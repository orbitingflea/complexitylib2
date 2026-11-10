/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Dictionary.SuccinctWhpProb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Small-Regime Array, In-Place Slot Permutation, and CSR Fallback Model

This module develops three pure building blocks for the with-high-probability fixed-capacity
succinct dynamic dictionary (`Cslib.DataStructure.Dictionary.SuccinctWhp`):

1. **Small-regime deterministic array (`SmallDictState`)**: when `n_max < whpThreshold c`, the
   dictionary stores up to `n_max` `(present, key, value)` triples scanned in
   `n_max < whpThreshold c` deterministic steps (`failureProb = 0`).
2. **In-place cycle-following slot rearrangement (`permuteByTarget`)**: rearranges `qArr` and `vArr`
   in place across `n_max` physical slots along any injective partial map `{s < n_max | active s} →
   Fin n_max`, using a single 1-bit `active` marker array and fixed `n_max`-iteration loops. Both
   `fastMode → fallbackMode` compaction and `fallbackMode → fastMode` self-healing instantiate this
   single primitive.
3. **Compressed-sparse-row (`CsrState`) fallback dictionary and overflow-free `GoodSeedOnState`
   checker**: stores arbitrary bucket loads `(X_0, …, X_{M - 1})` (`∑ X_b ≤ n_max`) in `1 · OPT +
   o(n_max)` bits via bucket prefix sums `fbStart[0 .. M]` plus Feistel quotients and values, with
   exact `Dynamic.step` refinement for **every** seed `θ` and an overflow-free decision procedure
   for `GoodSeedOnState`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.SmallDictState`, `smallScan`, `smallQuery`,
  `smallInsert`, `smallDelete`, `ValidSmallState`: deterministic small-regime dictionary model.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.permuteByTarget`: in-place cycle-following slot
  rearrangement.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.CsrState`, `csrQuery`, `csrInsert`, `csrDelete`,
  `ValidCsrState`, `checkBalancedBucketNat`, `checkGoodSeedOnState`: CSR fallback dictionary and
  self-healing eligibility checker.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.smallQuery_spec`, `smallInsert_spec`,
  `smallDelete_spec`: exact `Dynamic.step` refinement in the small regime.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.permuteByTarget_spec`: exact in-place bijection
  specification of `permuteByTarget`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.csrQuery_spec`, `csrInsert_spec`, `csrDelete_spec`,
  `checkGoodSeedOnState_spec`: exact `Dynamic.step` refinement in CSR fallback mode and exact
  equivalence with `GoodSeedOnState`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: Small-regime deterministic dictionary (`n_max < whpThreshold c`) -/

/-- Pure state of the small-regime bit-packed array dictionary (`0 .. n_max - 1`). -/
structure SmallDictState where
  /-- Occupancy bit (`0` = empty, non-zero = active) at slot `i < n_max`. -/
  present : ℕ → ℕ
  /-- Stored key `< U` at slot `i < n_max`. -/
  keys : ℕ → ℕ
  /-- Stored value `< V` at slot `i < n_max`. -/
  vals : ℕ → ℕ

/-- Initial empty `SmallDictState`. -/
@[expose] def emptySmallState : SmallDictState where
  present := fun _ => 0
  keys := fun _ => 0
  vals := fun _ => 0

/-- Single step of the `n_max`-slot scan at index `i`, maintaining `(foundIdx1, freeIdx1)` where `0`
encodes `none` and `idx + 1` encodes `some idx`. -/
@[expose] def smallScanStep (st : SmallDictState) (u_val i : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  if st.present i != 0 then
    if st.keys i == u_val && acc.1 == 0 then (i + 1, acc.2) else acc
  else
    if acc.2 == 0 then (acc.1, i + 1) else acc

/-- Prefix scan over `0 .. k - 1` returning `(foundIdx1, freeIdx1)`. -/
@[expose] def smallScan (st : SmallDictState) (u_val : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 => smallScanStep st u_val k (smallScan st u_val k)

/-- Small-regime lookup of `u_val`. -/
@[expose] def smallQuery (n_max : ℕ) (st : SmallDictState) (u_val : ℕ) : Option ℕ :=
  let (f1, _) := smallScan st u_val n_max
  if f1 = 0 then none else some (st.vals (f1 - 1))

/-- Small-regime insertion / overwrite of `(u_val, v_val)`. -/
@[expose] def smallInsert (n_max : ℕ) (st : SmallDictState) (u_val v_val : ℕ) : SmallDictState :=
  let (f1, free1) := smallScan st u_val n_max
  if f1 != 0 then
    { st with vals := Function.update st.vals (f1 - 1) v_val }
  else if free1 != 0 then
    let idx := free1 - 1
    { present := Function.update st.present idx 1
      keys := Function.update st.keys idx u_val
      vals := Function.update st.vals idx v_val }
  else st

/-- Small-regime deletion of `u_val`. -/
@[expose] def smallDelete (n_max : ℕ) (st : SmallDictState) (u_val : ℕ) : SmallDictState :=
  let (f1, _) := smallScan st u_val n_max
  if f1 != 0 then
    { st with present := Function.update st.present (f1 - 1) 0 }
  else st

/-- Representation invariant relating `SmallDictState` to `dict : Dictionary.State U`. -/
@[expose] def ValidSmallState (U V n_max : ℕ) (st : SmallDictState) (dict : State U) : Prop :=
  (∀ i < n_max, st.present i ≤ 1) ∧
  (∀ i < n_max, st.present i ≠ 0 → st.keys i < U ∧ st.vals i < V) ∧
  (∀ i < n_max, ∀ j < n_max, st.present i ≠ 0 → st.present j ≠ 0 →
    st.keys i = st.keys j → i = j) ∧
  ∀ u : Fin U,
    (dict u = none ↔ ∀ i < n_max, st.present i ≠ 0 → st.keys i ≠ u.val) ∧
    ∀ v, dict u = some v ↔ ∃ i < n_max, st.present i ≠ 0 ∧ st.keys i = u.val ∧ st.vals i = v

theorem validSmallState_empty (U V n_max : ℕ) :
    ValidSmallState U V n_max emptySmallState (Dictionary.empty U) := by
  refine ⟨fun _ _ => Nat.zero_le 1, fun _ _ h => absurd rfl h,
    fun _ _ _ _ h => absurd rfl h, fun u => ⟨?_, fun v => ?_⟩⟩
  · simp [Dictionary.empty, emptySmallState]
  · simp [Dictionary.empty, emptySmallState]

private theorem smallScan_props (st : SmallDictState) (u_val : ℕ) (k : ℕ) :
    let (f1, free1) := smallScan st u_val k
    (f1 = 0 ↔ ∀ i < k, st.present i ≠ 0 → st.keys i ≠ u_val) ∧
    (f1 ≠ 0 → f1 - 1 < k ∧ st.present (f1 - 1) ≠ 0 ∧ st.keys (f1 - 1) = u_val) ∧
    (free1 = 0 ↔ ∀ i < k, st.present i ≠ 0) ∧
    (free1 ≠ 0 → free1 - 1 < k ∧ st.present (free1 - 1) = 0) := by
  induction k with
  | zero =>
    simp [smallScan]
  | succ k ih =>
    dsimp only [smallScan]
    set p := smallScan st u_val k
    obtain ⟨hf0, hfnz, hfr0, hfrnz⟩ := ih
    dsimp only [smallScanStep]
    by_cases hp : st.present k != 0
    · have hpk : st.present k ≠ 0 := by simpa using hp
      simp only [hp, ↓reduceIte]
      by_cases hcond : (st.keys k == u_val && p.1 == 0) = true
      · simp only [Bool.and_eq_true, beq_iff_eq] at hcond
        obtain ⟨hku, hp10⟩ := hcond
        simp only [hku, hp10, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        refine ⟨⟨fun h => by omega, fun hall => absurd hku (hall k (Nat.lt_succ_self k) hpk)⟩,
          fun _ => ⟨by omega, hpk, hku⟩, ?_, ?_⟩
        · constructor
          · intro h0 i hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · exact hfr0.mp h0 i hlt
            · exact hpk
          · intro hall
            exact hfr0.mpr fun i hi => hall i (Nat.lt_succ_of_lt hi)
        · intro hnz
          obtain ⟨hlt, hz⟩ := hfrnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hz⟩
      · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
        have hnot : st.keys k ≠ u_val ∨ p.1 ≠ 0 := by
          simp only [Bool.and_eq_true, beq_iff_eq, not_and_or] at hcond
          exact hcond
        refine ⟨?_, ?_, ?_, ?_⟩
        · constructor
          · intro hp10 i hi hpi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · exact hf0.mp hp10 i hlt hpi
            · rcases hnot with hne | hnz
              · exact hne
              · exact absurd hp10 hnz
          · intro hall
            exact hf0.mpr fun i hi hpi => hall i (Nat.lt_succ_of_lt hi) hpi
        · intro hnz
          obtain ⟨hlt, hp', hk'⟩ := hfnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hp', hk'⟩
        · constructor
          · intro h0 i hi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · exact hfr0.mp h0 i hlt
            · exact hpk
          · intro hall
            exact hfr0.mpr fun i hi => hall i (Nat.lt_succ_of_lt hi)
        · intro hnz
          obtain ⟨hlt, hz⟩ := hfrnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hz⟩
    · have hpk0 : st.present k = 0 := by simpa using hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      by_cases hfr_z : p.2 == 0
      · have hp20 : p.2 = 0 := by simpa using hfr_z
        simp only [hfr_z, ↓reduceIte]
        refine ⟨?_, ?_, ⟨fun h => by omega, fun hall => absurd hpk0 (hall k (Nat.lt_succ_self k))⟩,
          fun _ => ⟨by omega, hpk0⟩⟩
        · constructor
          · intro hp10 i hi hpi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · exact hf0.mp hp10 i hlt hpi
            · exact absurd hpk0 hpi
          · intro hall
            exact hf0.mpr fun i hi hpi => hall i (Nat.lt_succ_of_lt hi) hpi
        · intro hnz
          obtain ⟨hlt, hp', hk'⟩ := hfnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hp', hk'⟩
      · have hp2nz : p.2 ≠ 0 := by simpa using hfr_z
        simp only [hfr_z, Bool.false_eq_true, ↓reduceIte]
        refine ⟨?_, ?_, ⟨fun h0 => absurd h0 hp2nz,
          fun hall => absurd hpk0 (hall k (Nat.lt_succ_self k))⟩, ?_⟩
        · constructor
          · intro hp10 i hi hpi
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
            · exact hf0.mp hp10 i hlt hpi
            · exact absurd hpk0 hpi
          · intro hall
            exact hf0.mpr fun i hi hpi => hall i (Nat.lt_succ_of_lt hi) hpi
        · intro hnz
          obtain ⟨hlt, hp', hk'⟩ := hfnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hp', hk'⟩
        · intro hnz
          obtain ⟨hlt, hz⟩ := hfrnz hnz
          exact ⟨Nat.lt_succ_of_lt hlt, hz⟩

/-- Small-regime lookup matches `dict u`. -/
theorem smallQuery_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) (u : Fin U) :
    smallQuery n_max st u.val = dict u := by
  obtain ⟨_, _, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallQuery
  set p := smallScan st u.val n_max
  by_cases hf0 : p.1 = 0
  · simp only [hf0, ↓reduceIte]
    exact ((hmap u).1.mpr (hsc.1.mp hf0)).symm
  · simp only [hf0, ↓reduceIte]
    obtain ⟨hlt, hp, hk⟩ := hsc.2.1 hf0
    symm
    exact ((hmap u).2 (st.vals (p.1 - 1))).mpr ⟨p.1 - 1, hlt, hp, hk, rfl⟩

/-- Small-regime deletion preserves `ValidSmallState` and refines `Function.update dict u none`. -/
theorem smallDelete_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) (u : Fin U) :
    ValidSmallState U V n_max (smallDelete n_max st u.val) (Function.update dict u none) := by
  obtain ⟨hp_le, hkv, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallDelete
  set p := smallScan st u.val n_max
  by_cases hfnz : p.1 != 0
  · have hf_ne : p.1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hidx_lt, hp_idx, hk_idx⟩ := hsc.2.1 hf_ne
    set idx := p.1 - 1
    refine ⟨?_, ?_, ?_, fun x => ⟨?_, fun v => ?_⟩⟩
    · intro i hi
      by_cases h : i = idx
      · subst h; simp
      · simp [h, hp_le i hi]
    · intro i hi hpi
      by_cases h : i = idx
      · subst h; simp at hpi
      · simp only [Function.update_of_ne h] at hpi
        exact hkv i hi hpi
    · intro i hi j hj hpi hpj heq
      have hni : i ≠ idx := fun h => by subst h; simp at hpi
      have hnj : j ≠ idx := fun h => by subst h; simp at hpj
      simp only [Function.update_of_ne hni, Function.update_of_ne hnj] at hpi hpj
      exact hinj i hi j hj hpi hpj heq
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, true_iff]
        intro i hi hpi hki
        have hni : i ≠ idx := fun h => by subst h; simp at hpi
        simp only [Function.update_of_ne hni] at hpi
        exact hni (hinj i hi idx hidx_lt hpi hp_idx (hki.trans hk_idx.symm))
      · rw [Function.update_of_ne hxu, (hmap x).1]
        constructor
        · intro hall i hi hpi
          have hni : i ≠ idx := fun h => by subst h; simp at hpi
          simp only [Function.update_of_ne hni] at hpi
          exact hall i hi hpi
        · intro hall i hi hpi
          by_cases h : i = idx
          · subst h
            rw [hk_idx]
            exact fun heq => hxu (Fin.ext heq.symm)
          · exact hall i hi (by simpa [h] using hpi)
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_exists, not_and]
        intro i hi hpi hki _
        have hni : i ≠ idx := fun h => by subst h; simp at hpi
        simp only [Function.update_of_ne hni] at hpi
        exact hni (hinj i hi idx hidx_lt hpi hp_idx (hki.trans hk_idx.symm))
      · rw [Function.update_of_ne hxu, (hmap x).2 v]
        constructor
        · rintro ⟨i, hi, hpi, hki, hvi⟩
          have hni : i ≠ idx := by
            intro h; subst h
            exact hxu (Fin.ext (hki.symm.trans hk_idx))
          exact ⟨i, hi, by simpa [hni] using hpi, hki, hvi⟩
        · rintro ⟨i, hi, hpi, hki, hvi⟩
          have hni : i ≠ idx := fun h => by subst h; simp at hpi
          exact ⟨i, hi, by simpa [hni] using hpi, hki, hvi⟩
  · have hf0 : p.1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hnone : dict u = none := (hmap u).1.mpr (hsc.1.mp hf0)
    have hupd : Function.update dict u none = dict := by
      ext x
      by_cases h : x = u
      · subst h; simp [hnone]
      · simp [h]
    rw [hupd]
    exact ⟨hp_le, hkv, hinj, hmap⟩

/-- Small-regime insertion preserves `ValidSmallState` and refines
`Function.update dict u (some v)` whenever `Dynamic.valid V n_max dict (.insert u v)`. -/
theorem smallInsert_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v)) :
    ValidSmallState U V n_max (smallInsert n_max st u.val v)
      (Function.update dict u (some v)) := by
  obtain ⟨hcap, hv_lt⟩ := hvalid
  obtain ⟨hp_le, hkv, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallInsert
  set p := smallScan st u.val n_max
  by_cases hfnz : p.1 != 0
  · have hf_ne : p.1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hidx_lt, hp_idx, hk_idx⟩ := hsc.2.1 hf_ne
    set idx := p.1 - 1
    refine ⟨hp_le, ?_, hinj, fun x => ⟨?_, fun w => ?_⟩⟩
    · intro i hi hpi
      by_cases h : i = idx
      · subst h; rw [hk_idx]; exact ⟨u.isLt, by simp [hv_lt]⟩
      · simp [h, (hkv i hi hpi).1, (hkv i hi hpi).2]
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
        exact ⟨idx, hidx_lt, hp_idx, hk_idx⟩
      · rw [Function.update_of_ne hxu, (hmap x).1]
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨idx, hidx_lt, hp_idx, hk_idx, by simp⟩
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          have hi_eq : i = idx := hinj i hi idx hidx_lt hpi hp_idx (hki.trans hk_idx.symm)
          subst hi_eq
          simpa using hwi
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        constructor
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          have hni : i ≠ idx := fun h => by
            subst h; exact hxu (Fin.ext (hki.symm.trans hk_idx))
          exact ⟨i, hi, hpi, hki, by simpa [hni] using hwi⟩
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          have hni : i ≠ idx := fun h => by
            subst h; exact hxu (Fin.ext (hki.symm.trans hk_idx))
          exact ⟨i, hi, hpi, hki, by simpa [hni] using hwi⟩
  · have hf0 : p.1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hnone_u : dict u = none := (hmap u).1.mpr (hsc.1.mp hf0)
    have hcard_lt : #(Dictionary.dom dict) < n_max := by
      rcases hcap with hlt | hsome
      · exact hlt
      · rw [hnone_u] at hsome; simp at hsome
    have hfr_ne : p.2 ≠ 0 := by
      intro hfr0
      have hall_act : ∀ i < n_max, st.present i ≠ 0 := hsc.2.2.1.mp hfr0
      let toKey : Fin n_max → Fin U := fun i =>
        ⟨st.keys i.val, (hkv i.val i.isLt (hall_act i.val i.isLt)).1⟩
      have hto_inj : Function.Injective toKey := fun i j heq =>
        Fin.ext (hinj i.val i.isLt j.val j.isLt (hall_act i.val i.isLt)
          (hall_act j.val j.isLt) (congrArg Fin.val heq))
      have hto_mem : ∀ i : Fin n_max, toKey i ∈ Dictionary.dom dict := by
        intro i
        by_contra hnot
        rw [Dictionary.notMem_dom_iff] at hnot
        exact (hmap (toKey i)).1.mp hnot i.val i.isLt (hall_act i.val i.isLt) rfl
      have hle : n_max ≤ #(Dictionary.dom dict) := by
        calc n_max = #(univ : Finset (Fin n_max)) := (Fintype.card_fin n_max).symm
          _ = #(univ.image toKey) := (Finset.card_image_of_injective _ hto_inj).symm
          _ ≤ #(Dictionary.dom dict) :=
              Finset.card_le_card (Finset.image_subset_iff.mpr fun i _ => hto_mem i)
      omega
    have hfr_b : (p.2 != 0) = true := by simpa using hfr_ne
    simp only [hfr_b, ↓reduceIte]
    obtain ⟨hidx_lt, hp0_idx⟩ := hsc.2.2.2 hfr_ne
    set idx := p.2 - 1
    refine ⟨?_, ?_, ?_, fun x => ⟨?_, fun w => ?_⟩⟩
    · intro i hi
      by_cases h : i = idx
      · subst h; simp
      · simp [h, hp_le i hi]
    · intro i hi hpi
      by_cases h : i = idx
      · subst h; simp [u.isLt, hv_lt]
      · simp only [Function.update_of_ne h] at hpi ⊢
        exact hkv i hi hpi
    · intro i hi j hj hpi hpj heq
      by_cases hi_eq : i = idx <;> by_cases hj_eq : j = idx
      · omega
      · subst hi_eq
        simp only [Function.update_self, Function.update_of_ne hj_eq] at hpj heq
        exact absurd heq.symm (hsc.1.mp hf0 j hj hpj)
      · subst hj_eq
        simp only [Function.update_self, Function.update_of_ne hi_eq] at hpi heq
        exact absurd heq (hsc.1.mp hf0 i hi hpi)
      · simp only [Function.update_of_ne hi_eq, Function.update_of_ne hj_eq] at hpi hpj heq
        exact hinj i hi j hj hpi hpj heq
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
        exact ⟨idx, hidx_lt, by simp, by simp⟩
      · rw [Function.update_of_ne hxu, (hmap x).1]
        constructor
        · intro hall i hi hpi
          by_cases h : i = idx
          · subst h; simp only [Function.update_self]; exact fun heq => hxu (Fin.ext heq.symm)
          · simp only [Function.update_of_ne h] at hpi ⊢
            exact hall i hi hpi
        · intro hall i hi hpi
          have hni : i ≠ idx := fun h => by subst h; exact hpi hp0_idx
          simpa [hni] using hall i hi (by simpa [hni] using hpi)
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨idx, hidx_lt, by simp, by simp, by simp⟩
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          by_cases h : i = idx
          · subst h; simpa using hwi
          · simp only [Function.update_of_ne h] at hpi hki
            exact absurd hki (hsc.1.mp hf0 i hi hpi)
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        constructor
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          have hni : i ≠ idx := fun h => by subst h; exact hpi hp0_idx
          exact ⟨i, hi, by simpa [hni] using hpi, by simpa [hni] using hki,
            by simpa [hni] using hwi⟩
        · rintro ⟨i, hi, hpi, hki, hwi⟩
          have hni : i ≠ idx := by
            intro h; subst h
            simp only [Function.update_self] at hki
            exact hxu (Fin.ext hki.symm)
          exact ⟨i, hi, by simpa [hni] using hpi, by simpa [hni] using hki,
            by simpa [hni] using hwi⟩

/-! ## Section 2: In-place cycle-following slot rearrangement (`permuteByTarget`) -/

/-- State tuple `(running, curDest, curQ, curV, act, qArr, vArr)` for `permuteInnerStep`. -/
abbrev PermChainState := Bool × ℕ × ℕ × ℕ × (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)

/-- Single step of a cycle-following chain along `dest`. -/
@[expose] def permuteInnerStep (dest : ℕ → ℕ) (st : PermChainState) : PermChainState :=
  let (running, curDest, curQ, curV, act, qArr, vArr) := st
  if !running then st
  else if act curDest then
    let nxtDest := dest curDest
    let nxtQ := qArr curDest
    let nxtV := vArr curDest
    (true, nxtDest, nxtQ, nxtV,
      Function.update act curDest false,
      Function.update qArr curDest curQ,
      Function.update vArr curDest curV)
  else
    (false, curDest, curQ, curV, act,
      Function.update qArr curDest curQ,
      Function.update vArr curDest curV)

/-- Run `k` steps of `permuteInnerStep`. -/
@[expose] def permuteInnerLoop (dest : ℕ → ℕ) : ℕ → PermChainState → PermChainState
  | 0, st => st
  | k + 1, st => permuteInnerLoop dest k (permuteInnerStep dest st)

/-- Outer step at source slot `s`: if `act s` is still `true`, extracts `(qArr s, vArr s)` and runs
`n_max` inner chain steps. -/
@[expose] def permuteOuterStep (n_max : ℕ) (dest : ℕ → ℕ) (s : ℕ)
    (triple : (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)) :
    (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) :=
  let (act, qArr, vArr) := triple
  if act s then
    let st₀ : PermChainState :=
      (true, dest s, qArr s, vArr s, Function.update act s false, qArr, vArr)
    let (_, _, _, _, act', qArr', vArr') := permuteInnerLoop dest n_max st₀
    (act', qArr', vArr')
  else triple

/-- Run `permuteOuterStep` across `s = 0 .. k - 1`. -/
@[expose] def permuteOuterLoop (n_max : ℕ) (dest : ℕ → ℕ) :
    ℕ → (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)
  | 0, triple => triple
  | k + 1, triple => permuteOuterStep n_max dest k (permuteOuterLoop n_max dest k triple)

/-- Rearrange `(qArr, vArr)` in place across `0 .. n_max - 1` so every `s < n_max` with
`act₀ s = true` lands at `dest s`. -/
@[expose] def permuteByTarget (n_max : ℕ) (dest : ℕ → ℕ) (act₀ : ℕ → Bool)
    (qArr vArr : ℕ → ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
  let (_, qArr', vArr') := permuteOuterLoop n_max dest n_max (actInit, qArr, vArr)
  (qArr', vArr')

private def PermOuterInv (_n_max : ℕ) (dest : ℕ → ℕ) (A₀ placed : Finset ℕ)
    (q₀ v₀ : ℕ → ℕ) (Q_bnd V_bnd : ℕ)
    (act : ℕ → Bool) (qArr vArr : ℕ → ℕ) : Prop :=
  placed ⊆ A₀ ∧
  (∀ i, act i = true ↔ i ∈ A₀ \ placed) ∧
  (∀ s ∈ A₀ \ placed, qArr s = q₀ s ∧ vArr s = v₀ s) ∧
  (∀ p ∈ placed, qArr (dest p) = q₀ p ∧ vArr (dest p) = v₀ p) ∧
  (∀ i, qArr i < Q_bnd ∧ vArr i < V_bnd)

private theorem permuteInnerLoop_spec {n_max : ℕ} {dest : ℕ → ℕ} {A₀ : Finset ℕ}
    (_hA₀ : ∀ s ∈ A₀, s < n_max)
    (hinj : ∀ s₁ ∈ A₀, ∀ s₂ ∈ A₀, dest s₁ = dest s₂ → s₁ = s₂)
    {q₀ v₀ : ℕ → ℕ} {Q_bnd V_bnd : ℕ}
    (hqv₀ : ∀ i, q₀ i < Q_bnd ∧ v₀ i < V_bnd) :
    ∀ (k : ℕ) (st : PermChainState) (placed : Finset ℕ),
      (if st.1 = false then
        PermOuterInv n_max dest A₀ placed q₀ v₀ Q_bnd V_bnd st.2.2.2.2.1 st.2.2.2.2.2.1
          st.2.2.2.2.2.2
      else
        ∃ p_cur ∈ A₀,
          p_cur ∉ placed ∧
          placed ⊆ A₀ ∧
          #(A₀ \ insert p_cur placed) + 1 ≤ k ∧
          st.2.1 = dest p_cur ∧
          st.2.2.1 = q₀ p_cur ∧
          st.2.2.2.1 = v₀ p_cur ∧
          (∀ i, st.2.2.2.2.1 i = true ↔ i ∈ A₀ \ insert p_cur placed) ∧
          (∀ s ∈ A₀ \ insert p_cur placed,
            st.2.2.2.2.2.1 s = q₀ s ∧ st.2.2.2.2.2.2 s = v₀ s) ∧
          (∀ p ∈ placed,
            st.2.2.2.2.2.1 (dest p) = q₀ p ∧ st.2.2.2.2.2.2 (dest p) = v₀ p) ∧
          (∀ i, st.2.2.2.2.2.1 i < Q_bnd ∧ st.2.2.2.2.2.2 i < V_bnd)) →
      let st' := permuteInnerLoop dest k st
      st'.1 = false ∧
      ∃ placed', placed ⊆ placed' ∧
        (∀ i, st.2.2.2.2.1 i = false → i ∈ A₀ → i ∈ placed') ∧
        PermOuterInv n_max dest A₀ placed' q₀ v₀ Q_bnd V_bnd st'.2.2.2.2.1 st'.2.2.2.2.2.1
          st'.2.2.2.2.2.2 := by
  intro k
  induction k with
  | zero =>
    intro st placed hinv
    rcases hrun : st.1 with _ | _
    · simp only [hrun, ↓reduceIte] at hinv
      refine ⟨hrun, placed, Subset.rfl, fun i hfalse hiA => ?_, hinv⟩
      by_contra hnp
      have ht := (hinv.2.1 i).mpr (mem_sdiff.mpr ⟨hiA, hnp⟩)
      rw [hfalse] at ht; cases ht
    · simp only [hrun, Bool.true_eq_false, ↓reduceIte] at hinv
      obtain ⟨_, _, _, _, hle0, _⟩ := hinv
      omega
  | succ k ih =>
    intro st placed hinv
    rcases st with ⟨running, curDest, curQ, curV, act, qArr, vArr⟩
    dsimp only [permuteInnerLoop]
    cases running
    · simp only [↓reduceIte] at hinv
      have hstep : permuteInnerStep dest (false, curDest, curQ, curV, act, qArr, vArr) =
          (false, curDest, curQ, curV, act, qArr, vArr) := rfl
      rw [hstep]
      exact ih (false, curDest, curQ, curV, act, qArr, vArr) placed (by simpa using hinv)
    · simp only [Bool.true_eq_false, ↓reduceIte] at hinv
      obtain ⟨p_cur, hp_in, hp_not, hpl_sub, hk_le, hd_eq, hq_eq, hv_eq, hact, hunext, hpl,
        hbnd⟩ := hinv
      subst hd_eq hq_eq hv_eq
      set extSet := insert p_cur placed
      have hext_sub : extSet ⊆ A₀ := insert_subset_iff.mpr ⟨hp_in, hpl_sub⟩
      have hbnd' : ∀ i,
          Function.update qArr (dest p_cur) (q₀ p_cur) i < Q_bnd ∧
          Function.update vArr (dest p_cur) (v₀ p_cur) i < V_bnd := by
        intro i
        by_cases h : i = dest p_cur
        · subst h; simp [(hqv₀ p_cur).1, (hqv₀ p_cur).2]
        · simp [h, (hbnd i).1, (hbnd i).2]
      have hpl' : ∀ p ∈ extSet,
          Function.update qArr (dest p_cur) (q₀ p_cur) (dest p) = q₀ p ∧
          Function.update vArr (dest p_cur) (v₀ p_cur) (dest p) = v₀ p := by
        intro p hp
        rcases mem_insert.mp hp with rfl | hp_old
        · simp
        · have hne_p : p ≠ p_cur := fun heq => hp_not (heq ▸ hp_old)
          have hne_d : dest p ≠ dest p_cur := fun hd =>
            hne_p (hinj p (hpl_sub hp_old) p_cur hp_in hd)
          simp [hne_d, (hpl p hp_old).1, (hpl p hp_old).2]
      dsimp only [permuteInnerStep]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hact_d : act (dest p_cur)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hd_not_sdiff : dest p_cur ∉ A₀ \ extSet := fun hm =>
          Bool.false_ne_true (hact_d.symm.trans ((hact _).mpr hm))
        have hout_step : PermOuterInv n_max dest A₀ extSet q₀ v₀ Q_bnd V_bnd
            act (Function.update qArr (dest p_cur) (q₀ p_cur))
            (Function.update vArr (dest p_cur) (v₀ p_cur)) := by
          refine ⟨hext_sub, hact, ?_, hpl', hbnd'⟩
          intro s hs
          have hne_s : s ≠ dest p_cur := fun heq => hd_not_sdiff (heq ▸ hs)
          simp [hne_s, (hunext s hs).1, (hunext s hs).2]
        obtain ⟨hrun', placed', hsub', hfalse', hout'⟩ := ih
          (false, dest p_cur, q₀ p_cur, v₀ p_cur, act,
            Function.update qArr (dest p_cur) (q₀ p_cur),
            Function.update vArr (dest p_cur) (v₀ p_cur))
          extSet (by simpa using hout_step)
        refine ⟨hrun', placed', (subset_insert _ _).trans hsub', fun i hfi hiA => ?_, hout'⟩
        exact hfalse' i hfi hiA
      · simp only [↓reduceIte]
        have hd_mem : dest p_cur ∈ A₀ \ extSet := (hact (dest p_cur)).mp hact_d
        have hd_in_A : dest p_cur ∈ A₀ := (mem_sdiff.mp hd_mem).1
        have hd_not_ext : dest p_cur ∉ extSet := (mem_sdiff.mp hd_mem).2
        have hqv_d := hunext (dest p_cur) hd_mem
        rw [hqv_d.1, hqv_d.2]
        have hcard_lt : #(A₀ \ insert (dest p_cur) extSet) < #(A₀ \ extSet) := by
          have hsdiff_eq : A₀ \ insert (dest p_cur) extSet = (A₀ \ extSet).erase (dest p_cur) := by
            ext x; simp [mem_sdiff, mem_insert, and_left_comm]
          rw [hsdiff_eq]
          exact card_erase_lt_of_mem hd_mem
        have hinv_nxt : ∃ p_nxt ∈ A₀,
            p_nxt ∉ extSet ∧
            extSet ⊆ A₀ ∧
            #(A₀ \ insert p_nxt extSet) + 1 ≤ k ∧
            dest (dest p_cur) = dest p_nxt ∧
            q₀ (dest p_cur) = q₀ p_nxt ∧
            v₀ (dest p_cur) = v₀ p_nxt ∧
            (∀ i, Function.update act (dest p_cur) false i = true ↔
              i ∈ A₀ \ insert p_nxt extSet) ∧
            (∀ s ∈ A₀ \ insert p_nxt extSet,
              Function.update qArr (dest p_cur) (q₀ p_cur) s = q₀ s ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) s = v₀ s) ∧
            (∀ p ∈ extSet,
              Function.update qArr (dest p_cur) (q₀ p_cur) (dest p) = q₀ p ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) (dest p) = v₀ p) ∧
            (∀ i,
              Function.update qArr (dest p_cur) (q₀ p_cur) i < Q_bnd ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) i < V_bnd) := by
          refine ⟨dest p_cur, hd_in_A, hd_not_ext, hext_sub, by omega, rfl, rfl, rfl,
            ?_, ?_, hpl', hbnd'⟩
          · intro i
            by_cases hi : i = dest p_cur
            · subst hi; simp
            · simp only [Function.update_of_ne hi, hact i, mem_sdiff, mem_insert, hi, false_or]
          · intro s hs
            have hne_s : s ≠ dest p_cur := fun h => by subst h; simp at hs
            have hs_old : s ∈ A₀ \ extSet := by
              rw [mem_sdiff, mem_insert] at hs
              exact mem_sdiff.mpr ⟨hs.1, fun h => hs.2 (Or.inr h)⟩
            simp [hne_s, (hunext s hs_old).1, (hunext s hs_old).2]
        obtain ⟨hrun', placed', hsub', hfalse', hout'⟩ := ih
          (true, dest (dest p_cur), q₀ (dest p_cur), v₀ (dest p_cur),
            Function.update act (dest p_cur) false,
            Function.update qArr (dest p_cur) (q₀ p_cur),
            Function.update vArr (dest p_cur) (v₀ p_cur))
          extSet (by simpa using hinv_nxt)
        refine ⟨hrun', placed', (subset_insert _ _).trans hsub', fun i hfi hiA => ?_, hout'⟩
        by_cases hi_d : i = dest p_cur
        · subst hi_d; rw [hact_d] at hfi; cases hfi
        · exact hfalse' i (by simpa [hi_d] using hfi) hiA

/-- **Exact in-place permutation theorem (`permuteByTarget_spec`)**:
if `dest` is injective on `A₀ = {s < n_max | act₀ s = true}` and maps `A₀` into `< n_max`, then
`permuteByTarget` places `(q₀ s, v₀ s)` at `dest s` for every `s ∈ A₀` while preserving global
value bounds `(Q_bnd, V_bnd)`. -/
theorem permuteByTarget_spec {n_max : ℕ} {dest : ℕ → ℕ} {act₀ : ℕ → Bool}
    {q₀ v₀ : ℕ → ℕ} {Q_bnd V_bnd : ℕ}
    (hinj : ∀ s₁ < n_max, ∀ s₂ < n_max, act₀ s₁ = true → act₀ s₂ = true →
      dest s₁ = dest s₂ → s₁ = s₂)
    (hqv₀ : ∀ i, q₀ i < Q_bnd ∧ v₀ i < V_bnd) :
    let (q', v') := permuteByTarget n_max dest act₀ q₀ v₀
    (∀ s < n_max, act₀ s = true → q' (dest s) = q₀ s ∧ v' (dest s) = v₀ s) ∧
    (∀ i, q' i < Q_bnd ∧ v' i < V_bnd) := by
  let A₀ : Finset ℕ := (range n_max).filter fun s => act₀ s = true
  have hA₀_lt : ∀ s ∈ A₀, s < n_max := fun s hs => mem_range.mp (mem_filter.mp hs).1
  have hinj_A : ∀ s₁ ∈ A₀, ∀ s₂ ∈ A₀, dest s₁ = dest s₂ → s₁ = s₂ := fun s₁ h₁ s₂ h₂ hd =>
    hinj s₁ (hA₀_lt s₁ h₁) s₂ (hA₀_lt s₂ h₂) (mem_filter.mp h₁).2 (mem_filter.mp h₂).2 hd
  let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
  have houter : ∀ k ≤ n_max,
      let (act_k, q_k, v_k) := permuteOuterLoop n_max dest k (actInit, q₀, v₀)
      ∃ placed, (∀ s ∈ A₀, s < k → s ∈ placed) ∧
        PermOuterInv n_max dest A₀ placed q₀ v₀ Q_bnd V_bnd act_k q_k v_k := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨∅, fun _ _ hs => absurd hs (Nat.not_lt_zero _), empty_subset _, ?_,
        fun _ _ => ⟨rfl, rfl⟩, fun _ hp => absurd hp (notMem_empty _), hqv₀⟩
      intro i
      simp [actInit, A₀]
    | succ k ih =>
      obtain ⟨placed, hcov, hout⟩ := ih (Nat.le_of_succ_le hk)
      dsimp only [permuteOuterLoop]
      set tr := permuteOuterLoop n_max dest k (actInit, q₀, v₀)
      dsimp only [permuteOuterStep]
      cases hact_k : tr.1 k
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨placed, fun s hsA hslt => ?_, hout⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hslt with hlt | rfl
        · exact hcov s hsA hlt
        · by_contra hnp
          have ht := (hout.2.1 s).mpr (mem_sdiff.mpr ⟨hsA, hnp⟩)
          rw [hact_k] at ht; cases ht
      · simp only [↓reduceIte]
        have hk_mem : k ∈ A₀ \ placed := (hout.2.1 k).mp hact_k
        have hk_A : k ∈ A₀ := (mem_sdiff.mp hk_mem).1
        have hk_np : k ∉ placed := (mem_sdiff.mp hk_mem).2
        have hqv_k := hout.2.2.1 k hk_mem
        have hcard_le : #(A₀ \ insert k placed) + 1 ≤ n_max := by
          have hsub : A₀ \ insert k placed ⊆ (range n_max).erase k := by
            intro x hx
            rw [mem_sdiff, mem_insert] at hx
            exact mem_erase.mpr ⟨fun heq => hx.2 (Or.inl heq), mem_range.mpr (hA₀_lt x hx.1)⟩
          have hc1 := card_le_card hsub
          have hc2 : #((range n_max).erase k) = n_max - 1 := by
            rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
          omega
        have hloop := permuteInnerLoop_spec hA₀_lt hinj_A hqv₀ n_max
          (true, dest k, tr.2.1 k, tr.2.2 k, Function.update tr.1 k false, tr.2.1, tr.2.2)
          placed <| by
            simp only [Bool.true_eq_false, ↓reduceIte]
            refine ⟨k, hk_A, hk_np, hout.1, hcard_le, rfl, hqv_k.1, hqv_k.2, ?_, ?_, hout.2.2.2.1,
              hout.2.2.2.2⟩
            · intro i
              by_cases hik : i = k
              · subst hik; simp
              · simp only [Function.update_of_ne hik, hout.2.1 i, mem_sdiff, mem_insert, hik,
                  false_or]
            · intro s hs
              have hs_old : s ∈ A₀ \ placed := by
                rw [mem_sdiff, mem_insert] at hs
                exact mem_sdiff.mpr ⟨hs.1, fun hp => hs.2 (Or.inr hp)⟩
              exact hout.2.2.1 s hs_old
        obtain ⟨_, placed', hpl_sub, hfalse_in, hout'⟩ := hloop
        refine ⟨placed', fun s hsA hslt => ?_, hout'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hslt with hlt | rfl
        · exact hpl_sub (hcov s hsA hlt)
        · exact hfalse_in s (by simp) hsA
  obtain ⟨placed, hcov, hout⟩ := houter n_max le_rfl
  dsimp only [permuteByTarget]
  refine ⟨fun s hs_lt hact_s => ?_, hout.2.2.2.2⟩
  have hsA : s ∈ A₀ := mem_filter.mpr ⟨mem_range.mpr hs_lt, hact_s⟩
  exact hout.2.2.2.1 s (hcov s hsA hs_lt)

/-! ## Section 3: Compressed-sparse-row (`CsrState`) fallback dictionary and `GoodSeedOnState` -/

/-- Compressed-sparse-row bucket fallback state over `M = numBucketsWhp n_max` Feistel buckets. -/
structure CsrState where
  /-- Bucket boundary prefix sums `fbStart 0 = 0 ≤ fbStart 1 ≤ … ≤ fbStart M ≤ n_max`. -/
  fbStart : ℕ → ℕ
  /-- Stored Feistel quotients `< 2 ^ quotBitsWhp U n_max`. -/
  qArr : ℕ → ℕ
  /-- Stored values `< V`. -/
  vArr : ℕ → ℕ

/-- Scan `len` slots starting at `lo` for `qArr (lo + k) == q_val`, returning `0` if absent or
`(lo + k) + 1` for the matching index. -/
@[expose] def csrScanRange (qArr : ℕ → ℕ) (lo q_val : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 =>
    let prev := csrScanRange qArr lo q_val len
    if prev != 0 then prev
    else if qArr (lo + len) == q_val then (lo + len) + 1
    else 0

/-- Shift `(qArr, vArr)` down by 1 across `i₀ .. i₀ + cnt - 1`
(`arr'[i₀ + k] = arr[i₀ + k + 1]`). -/
@[expose] def csrShiftDown (i₀ : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | cnt + 1, p =>
    let (q1, v1) := csrShiftDown i₀ cnt p
    let pos := i₀ + cnt
    (Function.update q1 pos (q1 (pos + 1)), Function.update v1 pos (v1 (pos + 1)))

/-- Shift `(qArr, vArr)` up by 1 from `N` down across `cnt` elements (`idx = N - k`). -/
@[expose] def csrShiftUp (N : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | cnt + 1, p =>
    let (q1, v1) := csrShiftUp N cnt p
    let idx := N - cnt
    (Function.update q1 idx (q1 (idx - 1)), Function.update v1 idx (v1 (idx - 1)))

/-- Adjust `fbStart (b + 1 + k)` by `-1` (if `dec = true`) or `+1` (if `dec = false`) for
`k = 0 .. cnt - 1`. -/
@[expose] def csrAdjustStarts (b : ℕ) (dec : Bool) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, f => f
  | cnt + 1, f =>
    let f1 := csrAdjustStarts b dec cnt f
    let idx := b + 1 + cnt
    Function.update f1 idx (if dec then f1 idx - 1 else f1 idx + 1)

/-- CSR fallback lookup of `(b, q_val)`. -/
@[expose] def csrQuery (csr : CsrState) (b q_val : ℕ) : Option ℕ :=
  let lo := csr.fbStart b
  let len := csr.fbStart (b + 1) - lo
  let f1 := csrScanRange csr.qArr lo q_val len
  if f1 = 0 then none else some (csr.vArr (f1 - 1))

/-- CSR fallback deletion of `(b, q_val)` across `M` buckets. -/
@[expose] def csrDelete (M : ℕ) (csr : CsrState) (b q_val : ℕ) : CsrState :=
  let lo := csr.fbStart b
  let len := csr.fbStart (b + 1) - lo
  let f1 := csrScanRange csr.qArr lo q_val len
  if f1 != 0 then
    let i₀ := f1 - 1
    let N := csr.fbStart M
    let (q', v') := csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)
    let fb' := csrAdjustStarts b true (M - b) csr.fbStart
    ⟨fb', q', v'⟩
  else csr

/-- CSR fallback insertion / overwrite of `(b, q_val, v_val)` across `M` buckets. -/
@[expose] def csrInsert (M : ℕ) (csr : CsrState) (b q_val v_val : ℕ) : CsrState :=
  let lo := csr.fbStart b
  let hi := csr.fbStart (b + 1)
  let f1 := csrScanRange csr.qArr lo q_val (hi - lo)
  if f1 != 0 then
    { csr with vArr := Function.update csr.vArr (f1 - 1) v_val }
  else
    let N := csr.fbStart M
    let (q1, v1) := csrShiftUp N (N - hi) (csr.qArr, csr.vArr)
    let q' := Function.update q1 hi q_val
    let v' := Function.update v1 hi v_val
    let fb' := csrAdjustStarts b false (M - b) csr.fbStart
    ⟨fb', q', v'⟩

/-- Exact invariant relating `CsrState` to `dict : Dictionary.State U` under bucket hash `h1`. -/
@[expose] def ValidCsrState (U V n_max : ℕ) (h1 : ℕ → ℕ) (csr : CsrState)
    (dict : State U) : Prop :=
  let M := numBucketsWhp n_max
  csr.fbStart 0 = 0 ∧
  (∀ b < M, csr.fbStart b ≤ csr.fbStart (b + 1)) ∧
  csr.fbStart M ≤ n_max ∧
  (∀ b < M, ∀ i, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) →
    let u_val := feistelReconstruct (bWhp n_max) h1 b (csr.qArr i)
    u_val < U ∧
    feistelBucket (bWhp n_max) h1 u_val = b ∧
    keyQuotient (bWhp n_max) u_val = csr.qArr i ∧
    csr.qArr i < 2 ^ quotBitsWhp U n_max ∧
    csr.vArr i < V) ∧
  (∀ b < M, ∀ i j, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) →
    csr.fbStart b ≤ j → j < csr.fbStart (b + 1) → csr.qArr i = csr.qArr j → i = j) ∧
  ∀ u : Fin U,
    let b := feistelBucket (bWhp n_max) h1 u.val
    let q := keyQuotient (bWhp n_max) u.val
    (dict u = none ↔ ∀ i, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) → csr.qArr i ≠ q) ∧
    ∀ v, dict u = some v ↔
      ∃ i, csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧ csr.qArr i = q ∧ csr.vArr i = v

theorem fbStart_mono_of_adj {M : ℕ} {f : ℕ → ℕ} (hadj : ∀ b < M, f b ≤ f (b + 1)) :
    ∀ a b, a ≤ b → b ≤ M → f a ≤ f b := by
  intro a b hab hbM
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hadj b (by omega))

private theorem csrScanRange_props (qArr : ℕ → ℕ) (lo q_val len : ℕ) :
    let f1 := csrScanRange qArr lo q_val len
    (f1 = 0 ↔ ∀ i, lo ≤ i → i < lo + len → qArr i ≠ q_val) ∧
    (f1 ≠ 0 → lo ≤ f1 - 1 ∧ f1 - 1 < lo + len ∧ qArr (f1 - 1) = q_val) := by
  induction len with
  | zero =>
    simp only [csrScanRange, Nat.add_zero, true_iff, ne_eq, not_true_eq_false, IsEmpty.forall_iff,
      and_true]
    intro i h1 h2; omega
  | succ len ih =>
    dsimp only [csrScanRange]
    set prev := csrScanRange qArr lo q_val len
    by_cases hp : prev != 0
    · have hp_ne : prev ≠ 0 := by simpa using hp
      simp only [hp, ↓reduceIte]
      obtain ⟨hlo_p, hlt_p, hq_p⟩ := ih.2 hp_ne
      refine ⟨⟨fun h0 => absurd h0 hp_ne, fun hall =>
        absurd hq_p (hall (prev - 1) hlo_p (by omega))⟩,
        fun _ => ⟨hlo_p, by omega, hq_p⟩⟩
    · have hp0 : prev = 0 := by simpa using hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      by_cases hqk : qArr (lo + len) == q_val
      · have hq_eq : qArr (lo + len) = q_val := by simpa using hqk
        simp only [hqk, ↓reduceIte]
        refine ⟨⟨fun h => by omega, fun hall =>
          absurd hq_eq (hall (lo + len) (by omega) (by omega))⟩,
          fun _ => ⟨by omega, by omega, hq_eq⟩⟩
      · have hq_ne : qArr (lo + len) ≠ q_val := by simpa using hqk
        simp only [hqk, Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨fun _ i hlo_i hlt_i => ?_, fun _ => by simp⟩, fun h => by simp at h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp (show i < lo + len + 1 by omega) with hlt' | rfl
        · exact ih.1.mp hp0 i hlo_i hlt'
        · exact hq_ne

theorem csrShiftDown_apply (i₀ cnt : ℕ) (qArr vArr : ℕ → ℕ) (x : ℕ) :
    (csrShiftDown i₀ cnt (qArr, vArr)).1 x =
      (if i₀ ≤ x ∧ x < i₀ + cnt then qArr (x + 1) else qArr x) ∧
    (csrShiftDown i₀ cnt (qArr, vArr)).2 x =
      (if i₀ ≤ x ∧ x < i₀ + cnt then vArr (x + 1) else vArr x) := by
  induction cnt generalizing x with
  | zero =>
    simp [csrShiftDown]
  | succ cnt ih =>
    dsimp only [csrShiftDown]
    by_cases hx : x = i₀ + cnt
    · subst hx
      have hn_next : ¬(i₀ ≤ i₀ + cnt + 1 ∧ i₀ + cnt + 1 < i₀ + cnt) := by omega
      have hyes : i₀ ≤ i₀ + cnt ∧ i₀ + cnt < i₀ + (cnt + 1) := by omega
      simp only [Function.update_self, (ih (i₀ + cnt + 1)).1, (ih (i₀ + cnt + 1)).2,
        hn_next, hyes, ↓reduceIte]
      exact ⟨rfl, rfl⟩
    · simp only [Function.update_of_ne hx, (ih x).1, (ih x).2]
      by_cases h1 : i₀ ≤ x ∧ x < i₀ + cnt
      · have h2 : i₀ ≤ x ∧ x < i₀ + (cnt + 1) := by omega
        simp [h1, h2]
      · have h2 : ¬(i₀ ≤ x ∧ x < i₀ + (cnt + 1)) := by omega
        simp [h1, h2]

theorem csrShiftUp_apply (N cnt : ℕ) (hcnt : cnt ≤ N) (qArr vArr : ℕ → ℕ) (x : ℕ) :
    (csrShiftUp N cnt (qArr, vArr)).1 x =
      (if N - cnt < x ∧ x ≤ N then qArr (x - 1) else qArr x) ∧
    (csrShiftUp N cnt (qArr, vArr)).2 x =
      (if N - cnt < x ∧ x ≤ N then vArr (x - 1) else vArr x) := by
  induction cnt generalizing x with
  | zero =>
    simp [csrShiftUp]
  | succ cnt ih =>
    have hcnt' : cnt ≤ N := by omega
    dsimp only [csrShiftUp]
    by_cases hx : x = N - cnt
    · subst hx
      have hn_prev : ¬(N - cnt < N - cnt - 1 ∧ N - cnt - 1 ≤ N) := by omega
      have hyes : N - (cnt + 1) < N - cnt ∧ N - cnt ≤ N := by omega
      simp only [Function.update_self, (ih hcnt' (N - cnt - 1)).1, (ih hcnt' (N - cnt - 1)).2,
        hn_prev, hyes, ↓reduceIte]
      exact ⟨rfl, rfl⟩
    · simp only [Function.update_of_ne hx, (ih hcnt' x).1, (ih hcnt' x).2]
      split_ifs <;> omega

private theorem csrAdjustStarts_apply (b : ℕ) (dec : Bool) (cnt : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    csrAdjustStarts b dec cnt f x =
      if b + 1 ≤ x ∧ x < b + 1 + cnt then
        (if dec then f x - 1 else f x + 1)
      else f x := by
  induction cnt generalizing x with
  | zero =>
    simp [csrAdjustStarts]
  | succ cnt ih =>
    dsimp only [csrAdjustStarts]
    by_cases hx : x = b + 1 + cnt
    · subst hx
      rw [Function.update_self, ih (b + 1 + cnt)]
      split_ifs <;> omega
    · rw [Function.update_of_ne hx, ih x]
      split_ifs <;> omega

/-- Exact bucket-slice bijection for `ValidCsrState`: for every `b : Fin (numBucketsWhp n_max)`,
`(Dictionary.dom dict).filter (feistelBucket = b)` has cardinality
`csr.fbStart (b + 1) - csr.fbStart b`, and `#(Dictionary.dom dict) = csr.fbStart M`. -/
theorem ValidCsrState.bucket_and_dom_card {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState}
    {dict : State U} (hv : ValidCsrState U V n_max h1 csr dict) :
    (∀ b : Fin (numBucketsWhp n_max),
      #((Dictionary.dom dict).filter fun u =>
        feistelBucket (bWhp n_max) h1 u.val = b.val) =
        csr.fbStart (b.val + 1) - csr.fbStart b.val) ∧
    #(Dictionary.dom dict) = csr.fbStart (numBucketsWhp n_max) := by
  obtain ⟨hfb0, hadj, _, hvalid_i, hinj, hmap⟩ := hv
  have hper_b : ∀ b : Fin (numBucketsWhp n_max),
      #((Dictionary.dom dict).filter fun u =>
        feistelBucket (bWhp n_max) h1 u.val = b.val) =
        csr.fbStart (b.val + 1) - csr.fbStart b.val := by
    intro b
    rcases Nat.eq_zero_or_pos U with rfl | hU_pos
    · have hemp : (Dictionary.dom dict).filter
          (fun u : Fin 0 => feistelBucket (bWhp n_max) h1 u.val = b.val) = ∅ := by
        ext x; exact Fin.elim0 x
      rw [hemp, card_empty]
      by_cases hlt : csr.fbStart b.val < csr.fbStart (b.val + 1)
      · exfalso
        have hu0 := (hvalid_i b.val b.isLt (csr.fbStart b.val) le_rfl hlt).1
        omega
      · have hle := hadj b.val b.isLt
        omega
    · let f : ℕ → Fin U := fun i =>
        if hi : csr.fbStart b.val ≤ i ∧ i < csr.fbStart (b.val + 1) then
          ⟨feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i),
            (hvalid_i b.val b.isLt i hi.1 hi.2).1⟩
        else ⟨0, hU_pos⟩
      have himg : (Finset.Ico (csr.fbStart b.val) (csr.fbStart (b.val + 1))).image f =
          (Dictionary.dom dict).filter fun u =>
            feistelBucket (bWhp n_max) h1 u.val = b.val := by
        ext u
        rw [mem_image, mem_filter, Dictionary.mem_dom_iff]
        constructor
        · rintro ⟨i, hi_ico, rfl⟩
          rw [mem_Ico] at hi_ico
          have hprops := hvalid_i b.val b.isLt i hi_ico.1 hi_ico.2
          have hf_eq : (f i).val = feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i) := by
            simp [f, hi_ico.1, hi_ico.2]
          have hsome : dict (f i) = some (csr.vArr i) := by
            apply ((hmap (f i)).2 (csr.vArr i)).mpr
            rw [hf_eq, hprops.2.1, hprops.2.2.1]
            exact ⟨i, hi_ico.1, hi_ico.2, rfl, rfl⟩
          rw [hf_eq]
          exact ⟨⟨csr.vArr i, hsome⟩, hprops.2.1⟩
        · rintro ⟨⟨v, hv_u⟩, hb_u⟩
          obtain ⟨i, hlo, hhi, hqi, _⟩ := ((hmap u).2 v).mp hv_u
          rw [hb_u] at hlo hhi
          refine ⟨i, mem_Ico.mpr ⟨hlo, hhi⟩, Fin.ext ?_⟩
          have hf_eq : (f i).val = feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i) := by
            simp [f, hlo, hhi]
          rw [hf_eq, hqi, ← hb_u]
          exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
      have hinj_f : Set.InjOn f (Finset.Ico (csr.fbStart b.val) (csr.fbStart (b.val + 1))) := by
        intro i hi j hj heq
        rw [mem_coe, mem_Ico] at hi hj
        have h1_eq : (f i).val = feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i) := by
          simp [f, hi.1, hi.2]
        have h2_eq : (f j).val = feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr j) := by
          simp [f, hj.1, hj.2]
        have hq_i := (hvalid_i b.val b.isLt i hi.1 hi.2).2.2.1
        have hq_j := (hvalid_i b.val b.isLt j hj.1 hj.2).2.2.1
        have hrec_eq : feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i) =
            feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr j) := by
          rw [← h1_eq, ← h2_eq, heq]
        have hq_eq : csr.qArr i = csr.qArr j := by
          rw [← hq_i, hrec_eq, hq_j]
        exact hinj b.val b.isLt i j hi.1 hi.2 hj.1 hj.2 hq_eq
      rw [← himg, Finset.card_image_of_injOn hinj_f, Nat.card_Ico]
  refine ⟨hper_b, ?_⟩
  have hpart : #(Dictionary.dom dict) =
      ∑ b : Fin (numBucketsWhp n_max),
        #((Dictionary.dom dict).filter fun u =>
          feistelBucket (bWhp n_max) h1 u.val = b.val) := by
    rw [Finset.card_eq_sum_ones]
    have h1_sum : ∀ u ∈ Dictionary.dom dict,
        (1 : ℕ) = ∑ b : Fin (numBucketsWhp n_max),
          if feistelBucket (bWhp n_max) h1 u.val = b.val then 1 else 0 := by
      intro u _
      let b₀ : Fin (numBucketsWhp n_max) :=
        ⟨feistelBucket (bWhp n_max) h1 u.val, feistelBucket_lt (bWhp n_max) h1 u.val⟩
      rw [Fintype.sum_eq_single b₀]
      · simp [b₀]
      · intro b hne
        have hv_ne : feistelBucket (bWhp n_max) h1 u.val ≠ b.val := fun h => hne (Fin.ext h.symm)
        simp [hv_ne]
    rw [Finset.sum_congr rfl h1_sum, Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun b => ?_
    rw [Finset.card_filter]
  have htel : ∀ k ≤ numBucketsWhp n_max,
      ∑ b ∈ range k, (csr.fbStart (b + 1) - csr.fbStart b) = csr.fbStart k := by
    intro k hk
    induction k with
    | zero => simp [hfb0]
    | succ k ih =>
      rw [sum_range_succ, ih (by omega)]
      have hle := hadj k (by omega)
      omega
  rw [hpart]
  simp_rw [hper_b]
  have htelM := htel (numBucketsWhp n_max) le_rfl
  rwa [← Fin.sum_univ_eq_sum_range (fun k => csr.fbStart (k + 1) - csr.fbStart k)
    (numBucketsWhp n_max)] at htelM

/-- CSR fallback lookup matches `dict u` for every seed `h1`. -/
theorem csrQuery_spec {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max h1 csr dict) (u : Fin U) :
    csrQuery csr (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val) =
      dict u := by
  obtain ⟨_, hadj, _, _, _, hmap⟩ := hv
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) h1 u.val
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hhi_eq : csr.fbStart b + (csr.fbStart (b + 1) - csr.fbStart b) = csr.fbStart (b + 1) := by
    omega
  have hsc := csrScanRange_props csr.qArr (csr.fbStart b) q
    (csr.fbStart (b + 1) - csr.fbStart b)
  dsimp only [csrQuery]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hf0 : f1 = 0
  · simp only [hf0, ↓reduceIte]
    have hall := hsc.1.mp hf0
    rw [hhi_eq] at hall
    exact ((hmap u).1.mpr hall).symm
  · simp only [hf0, ↓reduceIte]
    obtain ⟨hlo, hhi, hqi⟩ := hsc.2 hf0
    rw [hhi_eq] at hhi
    symm
    exact ((hmap u).2 (csr.vArr (f1 - 1))).mpr ⟨f1 - 1, hlo, hhi, hqi, rfl⟩

/-- CSR fallback deletion preserves `ValidCsrState` and refines `Function.update dict u none` for
every seed `h1`. -/
theorem csrDelete_spec {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max h1 csr dict) (u : Fin U) :
    ValidCsrState U V n_max h1
      (csrDelete (numBucketsWhp n_max) csr
        (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val))
      (Function.update dict u none) := by
  obtain ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
  have hmono := fbStart_mono_of_adj hadj
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hhi_eq : csr.fbStart b + (csr.fbStart (b + 1) - csr.fbStart b) = csr.fbStart (b + 1) := by
    omega
  have hsc := csrScanRange_props csr.qArr (csr.fbStart b) q
    (csr.fbStart (b + 1) - csr.fbStart b)
  dsimp only [csrDelete]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hfnz : f1 != 0
  · have hf_ne : f1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hlo_0, hhi_0, hq_0⟩ := hsc.2 hf_ne
    rw [hhi_eq] at hhi_0
    set i₀ := f1 - 1
    set N := csr.fbStart M
    have hi₀_lt_N : i₀ < N := hhi_0.trans_le (hmono (b + 1) M (by omega) le_rfl)
    set sh := csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)
    set fb' := csrAdjustStarts b true (M - b) csr.fbStart
    have hMb : b + 1 + (M - b) = M + 1 := by
      dsimp only [M, b] at hb_lt ⊢
      omega
    have hfb'_eq :
        ∀ x, fb' x = if b + 1 ≤ x ∧ x ≤ M then csr.fbStart x - 1 else csr.fbStart x := by
      intro x
      change csrAdjustStarts b true (M - b) csr.fbStart x = _
      rw [csrAdjustStarts_apply, hMb]
      simp only [↓reduceIte]
      split_ifs <;> omega
    have hsh_eq : ∀ x < N - 1,
        sh.1 x = csr.qArr (if x < i₀ then x else x + 1) ∧
        sh.2 x = csr.vArr (if x < i₀ then x else x + 1) := by
      intro x hx
      dsimp only [sh]
      obtain ⟨hqx, hvx⟩ := csrShiftDown_apply i₀ (N - 1 - i₀) csr.qArr csr.vArr x
      rw [hqx, hvx]
      split_ifs <;> omega
    have hge1_pos : ∀ x, b + 1 ≤ x → x ≤ M → 1 ≤ csr.fbStart x := by
      intro x hbx hxM
      have h1 : i₀ + 1 ≤ csr.fbStart (b + 1) := hhi_0
      have h2 : csr.fbStart (b + 1) ≤ csr.fbStart x := hmono (b + 1) x hbx hxM
      omega
    have horig_in : ∀ b' < M, ∀ i', fb' b' ≤ i' → i' < fb' (b' + 1) →
        let orig := if i' < i₀ then i' else i' + 1
        i' < N - 1 ∧ csr.fbStart b' ≤ orig ∧ orig < csr.fbStart (b' + 1) ∧ orig ≠ i₀ := by
      intro b' hb' i' hlo' hhi'
      dsimp only
      rw [hfb'_eq b'] at hlo'
      rw [hfb'_eq (b' + 1)] at hhi'
      have hb1_M : csr.fbStart (b' + 1) ≤ N := hmono (b' + 1) M (by omega) le_rfl
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · have hn1 : ¬(b + 1 ≤ b' ∧ b' ≤ M) := by omega
        have hn2 : ¬(b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M) := by omega
        simp only [hn1, hn2, ↓reduceIte] at hlo' hhi'
        have hle_b : csr.fbStart (b' + 1) ≤ csr.fbStart b := hmono (b' + 1) b (by omega) (by omega)
        have hi'_lt : i' < i₀ := by omega
        simp only [hi'_lt, ↓reduceIte]
        exact ⟨by omega, hlo', hhi', by omega⟩
      · have hn1 : ¬(b + 1 ≤ b ∧ b ≤ M) := by omega
        have hy2 : b + 1 ≤ b + 1 ∧ b + 1 ≤ M := by omega
        rw [ite_eq_right hn1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        have := hge1_pos (b + 1) le_rfl (by omega)
        by_cases hi'_lt : i' < i₀
        · simp only [hi'_lt, ↓reduceIte]
          exact ⟨by omega, hlo', by omega, by omega⟩
        · simp only [hi'_lt, ↓reduceIte]
          exact ⟨by omega, by omega, by omega, by omega⟩
      · have hy1 : b + 1 ≤ b' ∧ b' ≤ M := by omega
        have hy2 : b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M := by omega
        rw [ite_eq_left hy1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        have := hge1_pos b' (by omega) (by omega)
        have := hge1_pos (b' + 1) (by omega) (by omega)
        have hge_fb : csr.fbStart (b + 1) ≤ csr.fbStart b' :=
          hmono (b + 1) b' (by omega) (by omega)
        have hn_lt : ¬(i' < i₀) := by omega
        simp only [hn_lt, ↓reduceIte]
        exact ⟨by omega, by omega, by omega, by omega⟩
    dsimp only [ValidCsrState]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x => ⟨?_, fun v => ?_⟩⟩
    · rw [hfb'_eq 0]; split_ifs <;> omega
    · intro b' hb'
      change b' < M at hb'
      rw [hfb'_eq b', hfb'_eq (b' + 1)]
      have hle' := hadj b' hb'
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · split_ifs <;> omega
      · have := hge1_pos (b + 1) le_rfl (by omega)
        split_ifs <;> omega
      · have := hge1_pos b' (by omega) (by omega)
        have := hge1_pos (b' + 1) (by omega) (by omega)
        split_ifs <;> omega
    · change fb' M ≤ n_max
      rw [hfb'_eq M]
      have := hge1_pos M (by omega) le_rfl
      split_ifs <;> omega
    · intro b' hb' i' hlo' hhi'
      change b' < M at hb'
      obtain ⟨hi'_N, hor_lo, hor_hi, _⟩ := horig_in b' hb' i' hlo' hhi'
      obtain ⟨hq_eq, hv_eq⟩ := hsh_eq i' hi'_N
      rw [hq_eq, hv_eq]
      exact hvalid_i b' hb' _ hor_lo hor_hi
    · intro b' hb' i' j' hloi hhii hloj hhij hq_eq
      change b' < M at hb'
      obtain ⟨hi'_N, hlo1, hhi1, _⟩ := horig_in b' hb' i' hloi hhii
      obtain ⟨hj'_N, hlo2, hhi2, _⟩ := horig_in b' hb' j' hloj hhij
      rw [(hsh_eq i' hi'_N).1, (hsh_eq j' hj'_N).1] at hq_eq
      have horig_eq := hinj b' hb' _ _ hlo1 hhi1 hlo2 hhi2 hq_eq
      by_cases h1 : i' < i₀ <;> by_cases h2 : j' < i₀ <;>
        simp only [h1, h2, ↓reduceIte] at horig_eq <;> omega
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, true_iff]
        intro i' hlo' hhi' hq_eq
        obtain ⟨hi'_N, hor_lo, hor_hi, hor_ne⟩ := horig_in b hb_lt i' hlo' hhi'
        rw [(hsh_eq i' hi'_N).1] at hq_eq
        exact hor_ne (hinj b hb_lt _ i₀ hor_lo hor_hi hlo_0 hhi_0 (hq_eq.trans hq_0.symm))
      · rw [Function.update_of_ne hxu, (hmap x).1]
        set bx := feistelBucket (bWhp n_max) h1 x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        constructor
        · intro hall i' hlo' hhi'
          obtain ⟨hi'_N, hor_lo, hor_hi, _⟩ := horig_in bx hbx_lt i' hlo' hhi'
          rw [(hsh_eq i' hi'_N).1]
          exact hall _ hor_lo hor_hi
        · intro hall i hi_lo hi_hi hq_i
          have hi_ne_i₀ : i ≠ i₀ := by
            intro h; rw [h] at hi_lo hi_hi hq_i
            by_cases hbx_eq : bx = b
            · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx_eq
                (hq_i.symm.trans hq_0)))
            · rcases lt_or_gt_of_ne hbx_eq with hlt | hgt
              · have := hmono (bx + 1) b (by omega) (by omega); omega
              · have := hmono (b + 1) bx (by omega) (by omega); omega
          let i' := if i < i₀ then i else i - 1
          have hi'_in : fb' bx ≤ i' ∧ i' < fb' (bx + 1) ∧
              (if i' < i₀ then i' else i' + 1) = i := by
            dsimp only [i']
            rw [hfb'_eq bx, hfb'_eq (bx + 1)]
            rcases lt_trichotomy bx b with hlt | heq | hgt
            · have hle_b := hmono (bx + 1) b (by omega) (by omega)
              split_ifs <;> omega
            · rw [heq] at hi_lo hi_hi ⊢
              have := hge1_pos (b + 1) le_rfl (by omega)
              split_ifs <;> omega
            · have := hge1_pos bx (by omega) (by omega)
              have := hge1_pos (bx + 1) (by omega) (by omega)
              have hge_b := hmono (b + 1) bx (by omega) (by omega)
              split_ifs <;> omega
          obtain ⟨hi'_N, _, _, _⟩ := horig_in bx hbx_lt i' hi'_in.1 hi'_in.2.1
          apply hall i' hi'_in.1 hi'_in.2.1
          rw [(hsh_eq i' hi'_N).1, hi'_in.2.2]
          exact hq_i
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_exists, not_and]
        intro i' hlo' hhi' hq_eq _
        obtain ⟨hi'_N, hor_lo, hor_hi, hor_ne⟩ := horig_in b hb_lt i' hlo' hhi'
        rw [(hsh_eq i' hi'_N).1] at hq_eq
        exact hor_ne (hinj b hb_lt _ i₀ hor_lo hor_hi hlo_0 hhi_0 (hq_eq.trans hq_0.symm))
      · rw [Function.update_of_ne hxu, (hmap x).2 v]
        set bx := feistelBucket (bWhp n_max) h1 x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        constructor
        · rintro ⟨i, hi_lo, hi_hi, hq_i, hv_i⟩
          have hi_ne_i₀ : i ≠ i₀ := by
            intro h; rw [h] at hi_lo hi_hi hq_i
            by_cases hbx_eq : bx = b
            · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx_eq
                (hq_i.symm.trans hq_0)))
            · rcases lt_or_gt_of_ne hbx_eq with hlt | hgt
              · have := hmono (bx + 1) b (by omega) (by omega); omega
              · have := hmono (b + 1) bx (by omega) (by omega); omega
          let i' := if i < i₀ then i else i - 1
          have hi'_in : fb' bx ≤ i' ∧ i' < fb' (bx + 1) ∧
              (if i' < i₀ then i' else i' + 1) = i := by
            dsimp only [i']
            rw [hfb'_eq bx, hfb'_eq (bx + 1)]
            rcases lt_trichotomy bx b with hlt | heq | hgt
            · have hle_b := hmono (bx + 1) b (by omega) (by omega)
              split_ifs <;> omega
            · rw [heq] at hi_lo hi_hi ⊢
              have := hge1_pos (b + 1) le_rfl (by omega)
              split_ifs <;> omega
            · have := hge1_pos bx (by omega) (by omega)
              have := hge1_pos (bx + 1) (by omega) (by omega)
              have hge_b := hmono (b + 1) bx (by omega) (by omega)
              split_ifs <;> omega
          obtain ⟨hi'_N, _, _, _⟩ := horig_in bx hbx_lt i' hi'_in.1 hi'_in.2.1
          refine ⟨i', hi'_in.1, hi'_in.2.1, ?_, ?_⟩
          · rw [(hsh_eq i' hi'_N).1, hi'_in.2.2]; exact hq_i
          · rw [(hsh_eq i' hi'_N).2, hi'_in.2.2]; exact hv_i
        · rintro ⟨i', hlo', hhi', hq', hv'⟩
          obtain ⟨hi'_N, hor_lo, hor_hi, _⟩ := horig_in bx hbx_lt i' hlo' hhi'
          rw [(hsh_eq i' hi'_N).1] at hq'
          rw [(hsh_eq i' hi'_N).2] at hv'
          exact ⟨_, hor_lo, hor_hi, hq', hv'⟩
  · have hf0 : f1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hall := hsc.1.mp hf0
    rw [hhi_eq] at hall
    have hnone_u : dict u = none := (hmap u).1.mpr hall
    have hupd : Function.update dict u none = dict := by
      ext x
      by_cases h : x = u
      · subst h; simp [hnone_u]
      · simp [h]
    rw [hupd]
    exact ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩

theorem keyQuotient_lt_two_pow_quotBitsWhp {U n_max : ℕ} (hnU : n_max ≤ U) (u : Fin U) :
    keyQuotient (bWhp n_max) u.val < 2 ^ quotBitsWhp U n_max := by
  unfold keyQuotient
  refine Nat.div_lt_of_lt_mul ?_
  rw [mul_comm, ← Nat.pow_add, quotBitsWhp_add_bWhp hnU]
  rcases le_or_gt U 1 with hU1 | hU1
  · have hu0 : u.val = 0 := by omega
    rw [hu0]
    exact Nat.two_pow_pos _
  · exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)

/-- CSR fallback insertion preserves `ValidCsrState` and refines
`Function.update dict u (some v)` whenever `n_max ≤ U` and
`Dynamic.valid V n_max dict (.insert u v)`. -/
theorem csrInsert_spec {U V n_max : ℕ} (hnU : n_max ≤ U) {h1 : ℕ → ℕ} {csr : CsrState}
    {dict : State U} (hv : ValidCsrState U V n_max h1 csr dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v)) :
    ValidCsrState U V n_max h1
      (csrInsert (numBucketsWhp n_max) csr
        (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val) v)
      (Function.update dict u (some v)) := by
  have hdom_card := hv.bucket_and_dom_card.2
  obtain ⟨hcap, hv_lt⟩ := hvalid
  obtain ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
  have hq_lt : q < 2 ^ quotBitsWhp U n_max := keyQuotient_lt_two_pow_quotBitsWhp hnU u
  have hmono := fbStart_mono_of_adj hadj
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hhi_eq : csr.fbStart b + (csr.fbStart (b + 1) - csr.fbStart b) = csr.fbStart (b + 1) := by
    omega
  have hsc := csrScanRange_props csr.qArr (csr.fbStart b) q
    (csr.fbStart (b + 1) - csr.fbStart b)
  dsimp only [csrInsert]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hfnz : f1 != 0
  · have hf_ne : f1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hlo_0, hhi_0, hq_0⟩ := hsc.2 hf_ne
    rw [hhi_eq] at hhi_0
    set i₀ := f1 - 1
    dsimp only [ValidCsrState]
    refine ⟨hfb0, hadj, hfbM_le, ?_, hinj, fun x => ⟨?_, fun w => ?_⟩⟩
    · intro b' hb' i hlo hhi
      have hp := hvalid_i b' hb' i hlo hhi
      refine ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, ?_⟩
      by_cases h : i = i₀
      · subst h; simp [hv_lt]
      · simp [h, hp.2.2.2.2]
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
        exact ⟨i₀, hlo_0, hhi_0, hq_0⟩
      · rw [Function.update_of_ne hxu, (hmap x).1]
    · set bx := feistelBucket (bWhp n_max) h1 x.val
      have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
      by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨i₀, hlo_0, hhi_0, hq_0, by simp⟩
        · rintro ⟨i, hlo, hhi, hqi, hwi⟩
          have hi_eq : i = i₀ := hinj b hb_lt i i₀ hlo hhi hlo_0 hhi_0 (hqi.trans hq_0.symm)
          subst hi_eq
          simpa using hwi
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        constructor
        · rintro ⟨i, hlo, hhi, hqi, hwi⟩
          change csr.fbStart bx ≤ i at hlo
          change i < csr.fbStart (bx + 1) at hhi
          have hni : i ≠ i₀ := by
            intro h; rw [h] at hlo hhi hqi
            by_cases hbx : bx = b
            · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx
                (hqi.symm.trans hq_0)))
            · rcases lt_or_gt_of_ne hbx with hlt | hgt
              · have := hmono (bx + 1) b (by omega) (by omega); omega
              · have := hmono (b + 1) bx (by omega) (by omega); omega
          exact ⟨i, hlo, hhi, hqi, by simpa [hni] using hwi⟩
        · rintro ⟨i, hlo, hhi, hqi, hwi⟩
          change csr.fbStart bx ≤ i at hlo
          change i < csr.fbStart (bx + 1) at hhi
          have hni : i ≠ i₀ := by
            intro h; rw [h] at hlo hhi hqi
            by_cases hbx : bx = b
            · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx
                (hqi.symm.trans hq_0)))
            · rcases lt_or_gt_of_ne hbx with hlt | hgt
              · have := hmono (bx + 1) b (by omega) (by omega); omega
              · have := hmono (b + 1) bx (by omega) (by omega); omega
          exact ⟨i, hlo, hhi, hqi, by simpa [hni] using hwi⟩
  · have hf0 : f1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hall := hsc.1.mp hf0
    rw [hhi_eq] at hall
    have hnone_u : dict u = none := (hmap u).1.mpr hall
    set hi := csr.fbStart (b + 1)
    set N := csr.fbStart M
    have hhi_le_N : hi ≤ N := hmono (b + 1) M (by omega) le_rfl
    have hN_lt : N < n_max := by
      rcases hcap with hlt | hsome
      · rwa [hdom_card] at hlt
      · rw [hnone_u] at hsome; simp at hsome
    set sh := csrShiftUp N (N - hi) (csr.qArr, csr.vArr)
    set q' := Function.update sh.1 hi q
    set v' := Function.update sh.2 hi v
    set fb' := csrAdjustStarts b false (M - b) csr.fbStart
    have hMb : b + 1 + (M - b) = M + 1 := by
      dsimp only [M, b] at hb_lt ⊢
      omega
    have hfb'_eq :
        ∀ x, fb' x = if b + 1 ≤ x ∧ x ≤ M then csr.fbStart x + 1 else csr.fbStart x := by
      intro x
      change csrAdjustStarts b false (M - b) csr.fbStart x = _
      rw [csrAdjustStarts_apply, hMb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega
    have hqv'_eq : ∀ x ≤ N,
        (x < hi → q' x = csr.qArr x ∧ v' x = csr.vArr x) ∧
        (x = hi → q' x = q ∧ v' x = v) ∧
        (hi < x → q' x = csr.qArr (x - 1) ∧ v' x = csr.vArr (x - 1)) := by
      intro x hxN
      dsimp only [q', v', sh]
      obtain ⟨hqx, hvx⟩ := csrShiftUp_apply N (N - hi) (by omega) csr.qArr csr.vArr x
      refine ⟨fun hlt => ?_, fun heq => ?_, fun hgt => ?_⟩
      · have hne : x ≠ hi := by omega
        have hn : ¬(N - (N - hi) < x ∧ x ≤ N) := by omega
        simp [hne, hqx, hvx, hn]
      · subst heq; simp
      · have hne : x ≠ hi := by omega
        have hy : N - (N - hi) < x ∧ x ≤ N := by omega
        simp [hne, hqx, hvx, hy]
    have hrec_u : feistelReconstruct (bWhp n_max) h1 b q = u.val :=
      feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
    dsimp only [ValidCsrState]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x => ⟨?_, fun w => ?_⟩⟩
    · rw [hfb'_eq 0]; split_ifs <;> omega
    · intro b' hb'
      change b' < M at hb'
      rw [hfb'_eq b', hfb'_eq (b' + 1)]
      have hle' := hadj b' hb'
      split_ifs <;> omega
    · change fb' M ≤ n_max
      rw [hfb'_eq M]
      split_ifs <;> omega
    · intro b' hb' i' hlo' hhi'
      change b' < M at hb'
      rw [hfb'_eq b'] at hlo'
      rw [hfb'_eq (b' + 1)] at hhi'
      have hb1_N : csr.fbStart (b' + 1) ≤ N := hmono (b' + 1) M (by omega) le_rfl
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · have hn1 : ¬(b + 1 ≤ b' ∧ b' ≤ M) := by omega
        have hn2 : ¬(b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M) := by omega
        simp only [hn1, hn2, ↓reduceIte] at hlo' hhi'
        have hle_b := hmono (b' + 1) (b + 1) (by omega) (by omega)
        obtain ⟨hq_eq, hv_eq⟩ := (hqv'_eq i' (by omega)).1 (by omega)
        rw [hq_eq, hv_eq]
        exact hvalid_i b' hb' i' hlo' hhi'
      · have hn1 : ¬(b + 1 ≤ b ∧ b ≤ M) := by omega
        have hy2 : b + 1 ≤ b + 1 ∧ b + 1 ≤ M := by omega
        rw [ite_eq_right hn1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        rcases Nat.lt_succ_iff_lt_or_eq.mp hhi' with hlt_hi | rfl
        · obtain ⟨hq_eq, hv_eq⟩ := (hqv'_eq i' (by omega)).1 hlt_hi
          rw [hq_eq, hv_eq]
          exact hvalid_i b hb' i' hlo' hlt_hi
        · obtain ⟨hq_eq, hv_eq⟩ := (hqv'_eq hi hhi_le_N).2.1 rfl
          rw [hq_eq, hv_eq, hrec_u]
          exact ⟨u.isLt, rfl, rfl, hq_lt, hv_lt⟩
      · have hy1 : b + 1 ≤ b' ∧ b' ≤ M := by omega
        have hy2 : b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M := by omega
        rw [ite_eq_left hy1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        have hge_hi : hi ≤ csr.fbStart b' := hmono (b + 1) b' (by omega) (by omega)
        obtain ⟨hq_eq, hv_eq⟩ := (hqv'_eq i' (by omega)).2.2 (by omega)
        rw [hq_eq, hv_eq]
        exact hvalid_i b' hb' (i' - 1) (by omega) (by omega)
    · intro b' hb' i' j' hloi hhii hloj hhij hq_eq
      change b' < M at hb'
      rw [hfb'_eq b'] at hloi hloj
      rw [hfb'_eq (b' + 1)] at hhii hhij
      have hb1_N : csr.fbStart (b' + 1) ≤ N := hmono (b' + 1) M (by omega) le_rfl
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · have hn1 : ¬(b + 1 ≤ b' ∧ b' ≤ M) := by omega
        have hn2 : ¬(b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M) := by omega
        simp only [hn1, hn2, ↓reduceIte] at hloi hhii hloj hhij
        have hle_b := hmono (b' + 1) (b + 1) (by omega) (by omega)
        rw [((hqv'_eq i' (by omega)).1 (by omega)).1,
          ((hqv'_eq j' (by omega)).1 (by omega)).1] at hq_eq
        exact hinj b' hb' i' j' hloi hhii hloj hhij hq_eq
      · have hn1 : ¬(b + 1 ≤ b ∧ b ≤ M) := by omega
        have hy2 : b + 1 ≤ b + 1 ∧ b + 1 ≤ M := by omega
        rw [ite_eq_right hn1] at hloi hloj
        rw [ite_eq_left hy2] at hhii hhij
        rcases Nat.lt_succ_iff_lt_or_eq.mp hhii with hi_lt | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.mp hhij with hj_lt | rfl
        · rw [((hqv'_eq i' (by omega)).1 hi_lt).1,
            ((hqv'_eq j' (by omega)).1 hj_lt).1] at hq_eq
          exact hinj b hb' i' j' hloi hi_lt hloj hj_lt hq_eq
        · rw [((hqv'_eq i' (by omega)).1 hi_lt).1,
            ((hqv'_eq hi hhi_le_N).2.1 rfl).1] at hq_eq
          exact absurd hq_eq (hall i' hloi hi_lt)
        · rw [((hqv'_eq hi hhi_le_N).2.1 rfl).1,
            ((hqv'_eq j' (by omega)).1 hj_lt).1] at hq_eq
          exact absurd hq_eq.symm (hall j' hloj hj_lt)
        · rfl
      · have hy1 : b + 1 ≤ b' ∧ b' ≤ M := by omega
        have hy2 : b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M := by omega
        rw [ite_eq_left hy1] at hloi hloj
        rw [ite_eq_left hy2] at hhii hhij
        have hge_hi : hi ≤ csr.fbStart b' := hmono (b + 1) b' (by omega) (by omega)
        rw [((hqv'_eq i' (by omega)).2.2 (by omega)).1,
          ((hqv'_eq j' (by omega)).2.2 (by omega)).1] at hq_eq
        have heq1 := hinj b' hb' (i' - 1) (j' - 1) (by omega) (by omega) (by omega) (by omega) hq_eq
        omega
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
        refine ⟨hi, ?_, ?_, ((hqv'_eq hi hhi_le_N).2.1 rfl).1⟩
        · rw [hfb'_eq b]; split_ifs <;> omega
        · rw [hfb'_eq (b + 1)]; split_ifs <;> omega
      · rw [Function.update_of_ne hxu, (hmap x).1]
        set bx := feistelBucket (bWhp n_max) h1 x.val
        set qx := keyQuotient (bWhp n_max) x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        have hbx1_N : csr.fbStart (bx + 1) ≤ N := hmono (bx + 1) M (by omega) le_rfl
        rw [hfb'_eq bx, hfb'_eq (bx + 1)]
        rcases lt_trichotomy bx b with hlt_b | heq_b | hgt_b
        · have hn1 : ¬(b + 1 ≤ bx ∧ bx ≤ M) := by omega
          have hn2 : ¬(b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M) := by omega
          have hle_b := hmono (bx + 1) (b + 1) (by omega) (by omega)
          rw [ite_eq_right hn1, ite_eq_right hn2]
          exact ⟨fun hallx i hlo hhi => by
            rw [((hqv'_eq i (by omega)).1 (by omega)).1]; exact hallx i hlo hhi,
            fun hallx i hlo hhi => by
            have := hallx i hlo hhi; rwa [((hqv'_eq i (by omega)).1 (by omega)).1] at this⟩
        · have hn1 : ¬(b + 1 ≤ bx ∧ bx ≤ M) := by omega
          have hy2 : b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M := by omega
          rw [ite_eq_right hn1, ite_eq_left hy2]
          have hqx_ne : qx ≠ q := fun hqq =>
            hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq heq_b hqq))
          have hbx1_eq : csr.fbStart (bx + 1) = hi := by rw [heq_b]
          constructor
          · intro hallx i' hlo' hhi'
            rcases Nat.lt_succ_iff_lt_or_eq.mp (show i' < hi + 1 by omega)
              with hlt_hi | rfl
            · rw [((hqv'_eq i' (by omega)).1 hlt_hi).1]
              exact hallx i' hlo' (by omega)
            · rw [((hqv'_eq hi hhi_le_N).2.1 rfl).1]
              exact hqx_ne.symm
          · intro hallx i hlo hhi
            have hlt_hi : i < hi := by omega
            have h1 := hallx i hlo (by omega)
            rwa [((hqv'_eq i (by omega)).1 hlt_hi).1] at h1
        · have hy1 : b + 1 ≤ bx ∧ bx ≤ M := by omega
          have hy2 : b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M := by omega
          have hge_hi : hi ≤ csr.fbStart bx := hmono (b + 1) bx (by omega) (by omega)
          rw [ite_eq_left hy1, ite_eq_left hy2]
          constructor
          · intro hallx i' hlo' hhi'
            rw [((hqv'_eq i' (by omega)).2.2 (by omega)).1]
            exact hallx (i' - 1) (by omega) (by omega)
          · intro hallx i hlo hhi
            have h1 := hallx (i + 1) (by omega) (by omega)
            rwa [((hqv'_eq (i + 1) (by omega)).2.2 (by omega)).1, Nat.add_sub_cancel] at h1
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        rw [hfb'_eq b, hfb'_eq (b + 1)]
        have hn1 : ¬(b + 1 ≤ b ∧ b ≤ M) := by omega
        have hy2 : b + 1 ≤ b + 1 ∧ b + 1 ≤ M := by omega
        rw [ite_eq_right hn1, ite_eq_left hy2]
        constructor
        · rintro rfl
          exact ⟨hi, hle_fb, Nat.lt_succ_self hi,
            ((hqv'_eq hi hhi_le_N).2.1 rfl).1, ((hqv'_eq hi hhi_le_N).2.1 rfl).2⟩
        · rintro ⟨i', hlo', hhi', hq', hv'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hhi' with hlt_hi | rfl
          · rw [((hqv'_eq i' (by omega)).1 hlt_hi).1] at hq'
            exact absurd hq' (hall i' hlo' hlt_hi)
          · rw [((hqv'_eq hi hhi_le_N).2.1 rfl).2] at hv'
            exact hv'
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        set bx := feistelBucket (bWhp n_max) h1 x.val
        set qx := keyQuotient (bWhp n_max) x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        have hbx1_N : csr.fbStart (bx + 1) ≤ N := hmono (bx + 1) M (by omega) le_rfl
        rw [hfb'_eq bx, hfb'_eq (bx + 1)]
        rcases lt_trichotomy bx b with hlt_b | heq_b | hgt_b
        · have hn1 : ¬(b + 1 ≤ bx ∧ bx ≤ M) := by omega
          have hn2 : ¬(b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M) := by omega
          have hle_b := hmono (bx + 1) (b + 1) (by omega) (by omega)
          rw [ite_eq_right hn1, ite_eq_right hn2]
          constructor
          · rintro ⟨i, hlo, hhi, hqi, hwi⟩
            obtain ⟨hqe, hve⟩ := (hqv'_eq i (by omega)).1 (by omega)
            exact ⟨i, hlo, hhi, hqe.trans hqi, hve.trans hwi⟩
          · rintro ⟨i, hlo, hhi, hqi, hwi⟩
            obtain ⟨hqe, hve⟩ := (hqv'_eq i (by omega)).1 (by omega)
            exact ⟨i, hlo, hhi, hqe.symm.trans hqi, hve.symm.trans hwi⟩
        · have hn1 : ¬(b + 1 ≤ bx ∧ bx ≤ M) := by omega
          have hy2 : b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M := by omega
          rw [ite_eq_right hn1, ite_eq_left hy2]
          have hqx_ne : qx ≠ q := fun hqq =>
            hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq heq_b hqq))
          have hbx1_eq : csr.fbStart (bx + 1) = hi := by rw [heq_b]
          constructor
          · rintro ⟨i, hlo, hhi, hqi, hwi⟩
            have hlt_hi : i < hi := by omega
            obtain ⟨hqe, hve⟩ := (hqv'_eq i (by omega)).1 hlt_hi
            exact ⟨i, hlo, by omega, hqe.trans hqi, hve.trans hwi⟩
          · rintro ⟨i', hlo', hhi', hqi', hwi'⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp (show i' < hi + 1 by omega)
              with hlt_hi | rfl
            · obtain ⟨hqe, hve⟩ := (hqv'_eq i' (by omega)).1 hlt_hi
              exact ⟨i', hlo', by omega, hqe.symm.trans hqi',
                hve.symm.trans hwi'⟩
            · rw [((hqv'_eq hi hhi_le_N).2.1 rfl).1] at hqi'
              exact absurd hqi'.symm hqx_ne
        · have hy1 : b + 1 ≤ bx ∧ bx ≤ M := by omega
          have hy2 : b + 1 ≤ bx + 1 ∧ bx + 1 ≤ M := by omega
          have hge_hi : hi ≤ csr.fbStart bx := hmono (b + 1) bx (by omega) (by omega)
          simp only [hy1, hy2, and_self, ↓reduceIte]
          constructor
          · rintro ⟨i, hlo, hhi, hqi, hwi⟩
            obtain ⟨hqe, hve⟩ := (hqv'_eq (i + 1) (by omega)).2.2 (by omega)
            exact ⟨i + 1, by omega, by omega, by simpa using hqe.trans hqi,
              by simpa using hve.trans hwi⟩
          · rintro ⟨i', hlo', hhi', hqi', hwi'⟩
            obtain ⟨hqe, hve⟩ := (hqv'_eq i' (by omega)).2.2 (by omega)
            exact ⟨i' - 1, by omega, by omega, hqe.symm.trans hqi', hve.symm.trans hwi'⟩

/-! ### Overflow-free `GoodSeedOnState` decision & salt-discovery procedure on `CsrState` -/

/-- Overflow-free single-bucket load-balance test (`M * X_b ≤ N + M * δ ∧ N ≤ M * X_b + M * δ`)
using only division and remainder `< max (N + 1) M`. -/
@[expose] def checkBalancedBucketNat (M δ N X_b : ℕ) : Bool :=
  let qN := N / M
  let rN := N % M
  let lb := if rN == 0 then qN - δ else (qN + 1) - δ
  decide (X_b ≤ qN + δ) && decide (lb ≤ X_b)

theorem checkBalancedBucketNat_eq_true_iff {M δ N X_b : ℕ} (hM : 0 < M) :
    checkBalancedBucketNat M δ N X_b = true ↔
      (M * X_b ≤ N + M * δ ∧ N ≤ M * X_b + M * δ) := by
  unfold checkBalancedBucketNat
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  have hdiv := Nat.div_add_mod N M
  have hmod_lt : N % M < M := Nat.mod_lt N hM
  set qN := N / M
  set rN := N % M
  constructor
  · rintro ⟨hub, hlb⟩
    refine ⟨?_, ?_⟩
    · calc M * X_b ≤ M * (qN + δ) := Nat.mul_le_mul_left M hub
        _ = M * qN + M * δ := Nat.mul_add M qN δ
        _ ≤ (M * qN + rN) + M * δ := by omega
        _ = N + M * δ := by rw [hdiv]
    · by_cases hr0 : rN == 0
      · have hr_eq : rN = 0 := by simpa using hr0
        simp only [hr0, ↓reduceIte] at hlb
        have hq_le : qN ≤ X_b + δ := by omega
        calc N = M * qN + 0 := by rw [← hr_eq, hdiv]
          _ = M * qN := Nat.add_zero _
          _ ≤ M * (X_b + δ) := Nat.mul_le_mul_left M hq_le
          _ = M * X_b + M * δ := Nat.mul_add M X_b δ
      · have hr_pos : 0 < rN := by
          have hne : rN ≠ 0 := by simpa using hr0
          omega
        simp only [hr0, Bool.false_eq_true, ↓reduceIte] at hlb
        have hq1_le : qN + 1 ≤ X_b + δ := by omega
        calc N = M * qN + rN := hdiv.symm
          _ ≤ M * qN + M := by omega
          _ = M * (qN + 1) := by ring
          _ ≤ M * (X_b + δ) := Nat.mul_le_mul_left M hq1_le
          _ = M * X_b + M * δ := Nat.mul_add M X_b δ
  · rintro ⟨hub, hlb⟩
    refine ⟨?_, ?_⟩
    · by_contra hgt
      have hge1 : qN + δ + 1 ≤ X_b := by omega
      have hmul : M * (qN + δ + 1) ≤ M * X_b := Nat.mul_le_mul_left M hge1
      have hexp : M * (qN + δ + 1) = M * qN + M * δ + M := by ring
      omega
    · by_cases hr0 : rN == 0
      · have hr_eq : rN = 0 := by simpa using hr0
        simp only [hr0, ↓reduceIte]
        have hN_eq : N = M * qN := by omega
        rw [hN_eq, ← Nat.mul_add] at hlb
        have hle := Nat.le_of_mul_le_mul_left hlb hM
        omega
      · have hr_pos : 0 < rN := by
          have hne : rN ≠ 0 := by simpa using hr0
          omega
        simp only [hr0, Bool.false_eq_true, ↓reduceIte]
        by_contra hlt
        have hle_q : X_b + δ ≤ qN := by omega
        have hmul : M * (X_b + δ) ≤ M * qN := Nat.mul_le_mul_left M hle_q
        rw [Nat.mul_add] at hmul
        omega

/-- Scan `b = 0 .. k - 1` to find the bucket `b` satisfying
`fbStart b ≤ i ∧ i < fbStart (b + 1)`. -/
@[expose] def csrBucketOfIdx (fbStart : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if fbStart k ≤ i && i < fbStart (k + 1) then k
    else csrBucketOfIdx fbStart i k

theorem csrBucketOfIdx_spec {M : ℕ} {fbStart : ℕ → ℕ} (h0 : fbStart 0 = 0)
    (_hadj : ∀ b < M, fbStart b ≤ fbStart (b + 1)) :
    ∀ k ≤ M, ∀ i < fbStart k,
      let b := csrBucketOfIdx fbStart i k
      b < k ∧ fbStart b ≤ i ∧ i < fbStart (b + 1) := by
  intro k hk
  induction k with
  | zero =>
    intro i hi; rw [h0] at hi; exact absurd hi (Nat.not_lt_zero _)
  | succ k ih =>
    intro i hi
    dsimp only [csrBucketOfIdx]
    by_cases hcond : (fbStart k ≤ i && i < fbStart (k + 1)) = true
    · simp only [hcond, ↓reduceIte]
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
      exact ⟨Nat.lt_succ_self k, hcond.1, hcond.2⟩
    · simp only [hcond, Bool.false_eq_true, ↓reduceIte]
      have hlt_k : i < fbStart k := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and_or] at hcond
        rcases hcond with h1 | h2 <;> omega
      obtain ⟨hb_lt, hlo, hhi⟩ := ih (Nat.le_of_succ_le hk) i hlt_k
      exact ⟨Nat.lt_succ_of_lt hb_lt, hlo, hhi⟩

/-- Check all buckets `0 .. k - 1` for
`checkBalancedBucketNat M δ N (fbStart (b + 1) - fbStart b)`. -/
@[expose] def checkAllBalancedCsr (M δ N : ℕ) (fbStart : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    checkAllBalancedCsr M δ N fbStart k &&
      checkBalancedBucketNat M δ N (fbStart (k + 1) - fbStart k)

/-- Check `rKeyOf j != rKeyOf i` across `j = 0 .. k - 1`. -/
@[expose] def checkNoEqBefore (f : ℕ → ℕ) (target : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkNoEqBefore f target k && (f k != target)

/-- Check pairwise distinctness of `f` on `0 .. k - 1`. -/
@[expose] def checkPairwiseDistinctOn (f : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkPairwiseDistinctOn f k && checkNoEqBefore f (f k) k

private theorem checkNoEqBefore_iff (f : ℕ → ℕ) (target k : ℕ) :
    checkNoEqBefore f target k = true ↔ ∀ j < k, f j ≠ target := by
  induction k with
  | zero => simp [checkNoEqBefore]
  | succ k ih =>
    simp only [checkNoEqBefore, Bool.and_eq_true, ih, bne_iff_ne]
    constructor
    · rintro ⟨h1, h2⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact h1 j hlt
      · exact h2
    · intro hall
      exact ⟨fun j hj => hall j (Nat.lt_succ_of_lt hj), hall k (Nat.lt_succ_self k)⟩

private theorem checkPairwiseDistinctOn_iff (f : ℕ → ℕ) (k : ℕ) :
    checkPairwiseDistinctOn f k = true ↔ ∀ i < k, ∀ j < k, f i = f j → i = j := by
  induction k with
  | zero => simp [checkPairwiseDistinctOn]
  | succ k ih =>
    simp only [checkPairwiseDistinctOn, Bool.and_eq_true, ih, checkNoEqBefore_iff]
    constructor
    · rintro ⟨hp, hnew⟩ i hi j hj heq
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl <;>
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hp i hi' j hj' heq
      · exact absurd heq (hnew i hi')
      · exact absurd heq.symm (hnew j hj')
      · rfl
    · intro hinj
      refine ⟨fun i hi j hj heq => hinj i (Nat.lt_succ_of_lt hi) j (Nat.lt_succ_of_lt hj) heq,
        fun j hj heq => ?_⟩
      have := hinj j (Nat.lt_succ_of_lt hj) k (Nat.lt_succ_self k) heq
      omega

/-- Search `s = 0 .. k - 1` for the first salt `s` making `fpAt s` pairwise distinct on
`lo .. lo + len - 1`, returning `0` if none exists or `s + 1` if found. -/
@[expose] def findSaltInRange (fpAt : ℕ → ℕ → ℕ) (lo len : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 =>
    let prev := findSaltInRange fpAt lo len s
    if prev != 0 then prev
    else if checkPairwiseDistinctOn (fun t => fpAt s (lo + t)) len then s + 1
    else 0

private theorem findSaltInRange_props (fpAt : ℕ → ℕ → ℕ) (lo len sMax : ℕ) :
    let res := findSaltInRange fpAt lo len sMax
    (res = 0 ↔ ∀ s < sMax, ¬(∀ i < len, ∀ j < len, fpAt s (lo + i) = fpAt s (lo + j) → i = j)) ∧
    (res ≠ 0 → res - 1 < sMax ∧
      ∀ i < len, ∀ j < len, fpAt (res - 1) (lo + i) = fpAt (res - 1) (lo + j) → i = j) := by
  induction sMax with
  | zero => simp [findSaltInRange]
  | succ s ih =>
    dsimp only [findSaltInRange]
    set prev := findSaltInRange fpAt lo len s
    by_cases hp : prev != 0
    · have hp_ne : prev ≠ 0 := by simpa using hp
      simp only [hp, ↓reduceIte]
      obtain ⟨hlt_s, hinj_p⟩ := ih.2 hp_ne
      refine ⟨⟨fun h0 => absurd h0 hp_ne, fun hall =>
        absurd hinj_p (hall (prev - 1) (Nat.lt_succ_of_lt hlt_s))⟩,
        fun _ => ⟨Nat.lt_succ_of_lt hlt_s, hinj_p⟩⟩
    · have hp0 : prev = 0 := by simpa using hp
      simp only [hp, Bool.false_eq_true, ↓reduceIte]
      cases hchk : checkPairwiseDistinctOn (fun t => fpAt s (lo + t)) len
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hnot_s : ¬(∀ i < len, ∀ j < len, fpAt s (lo + i) = fpAt s (lo + j) → i = j) := by
          intro h; exact Bool.false_ne_true (hchk.symm.trans
            ((checkPairwiseDistinctOn_iff (fun t => fpAt s (lo + t)) len).mpr h))
        refine ⟨⟨fun _ s' hs' => ?_, fun _ => by simp⟩, fun h => by simp at h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hs' with hlt' | rfl
        · exact ih.1.mp hp0 s' hlt'
        · exact hnot_s
      · simp only [↓reduceIte]
        have hinj_s := (checkPairwiseDistinctOn_iff (fun t => fpAt s (lo + t)) len).mp hchk
        refine ⟨⟨fun h => by omega, fun hall =>
          absurd hinj_s (hall s (Nat.lt_succ_self s))⟩,
          fun _ => ⟨Nat.lt_succ_self s, hinj_s⟩⟩

/-- Pure overflow-free `GoodSeedOnState` check and per-bucket collision-free salt finder on
`CsrState`. Returns `(ok, saltOfBucket)`. -/
@[expose] def checkGoodSeedOnState (c U n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) :
    Bool × (ℕ → ℕ) :=
  let M := numBucketsWhp n_max
  let N := csr.fbStart M
  let h1 := bktHash c U n_max θ.1
  let keyValAt : ℕ → ℕ := fun i =>
    let b := csrBucketOfIdx csr.fbStart i M
    feistelReconstruct (bWhp n_max) h1 b (csr.qArr i)
  let rKeyAt : ℕ → ℕ := fun i =>
    if h : keyValAt i < U then fpReducedKey c U n_max θ.2 ⟨keyValAt i, h⟩ else 0
  let fpAt : ℕ → ℕ → ℕ := fun s i =>
    if hs : s < sMaxWhp c n_max then
      if hu : keyValAt i < U then fpHash c U n_max θ.2 ⟨s, hs⟩ ⟨keyValAt i, hu⟩ else 0
    else 0
  let okBal := checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M
  let okInj := checkPairwiseDistinctOn rKeyAt N
  let salt1Of : ℕ → ℕ := fun b =>
    findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)
  let allSaltsFound : ℕ → Bool := Nat.rec true fun b prev => prev && (salt1Of b != 0)
  (okBal && okInj && allSaltsFound M, fun b => salt1Of b - 1)

private theorem checkAllBalancedCsr_iff (M δ N : ℕ) (fbStart : ℕ → ℕ) (k : ℕ) :
    checkAllBalancedCsr M δ N fbStart k = true ↔
      ∀ b < k, checkBalancedBucketNat M δ N (fbStart (b + 1) - fbStart b) = true := by
  induction k with
  | zero => simp [checkAllBalancedCsr]
  | succ k ih =>
    simp only [checkAllBalancedCsr, Bool.and_eq_true, ih]
    constructor
    · rintro ⟨h1, h2⟩ b hb
      rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
      · exact h1 b hlt
      · exact h2
    · intro hall
      exact ⟨fun b hb => hall b (Nat.lt_succ_of_lt hb), hall k (Nat.lt_succ_self k)⟩

theorem csrBucketOfIdx_eq_of_in_range {M : ℕ} {fbStart : ℕ → ℕ}
    (h0 : fbStart 0 = 0) (hadj : ∀ b < M, fbStart b ≤ fbStart (b + 1))
    {b i : ℕ} (hb : b < M) (hlo : fbStart b ≤ i) (hhi : i < fbStart (b + 1)) :
    csrBucketOfIdx fbStart i M = b := by
  have hmono := fbStart_mono_of_adj hadj
  have hi_M : i < fbStart M := hhi.trans_le (hmono (b + 1) M (by omega) le_rfl)
  obtain ⟨hb'_lt, hlo', hhi'⟩ := csrBucketOfIdx_spec h0 hadj M le_rfl i hi_M
  set b' := csrBucketOfIdx fbStart i M
  rcases lt_trichotomy b' b with hlt | heq | hgt
  · have := hmono (b' + 1) b (by omega) (by omega); omega
  · exact heq
  · have := hmono (b + 1) b' (by omega) (by omega); omega

/-- **Exact soundness and completeness of `checkGoodSeedOnState`**:
for any `ValidCsrState`, `(checkGoodSeedOnState c U n_max θ csr).1 = true ↔
GoodSeedOnState c U n_max θ dict`, and when `true`, `(checkGoodSeedOnState ...).2 b` is a valid
collision-free salt `< sMaxWhp c n_max` for every bucket `b`. -/
theorem checkGoodSeedOnState_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict) :
    let (ok, salts) := checkGoodSeedOnState c U n_max θ csr
    (ok = true ↔ GoodSeedOnState c U n_max θ dict) ∧
    (ok = true → ∀ b : Fin (numBucketsWhp n_max),
      ∃ hs : salts b.val < sMaxWhp c n_max,
        Set.InjOn (fpHash c U n_max θ.2 ⟨salts b.val, hs⟩)
          ((Dictionary.dom dict).filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) := by
  obtain ⟨hcard_b, hcard_dom⟩ := hv.bucket_and_dom_card
  obtain ⟨hfb0, hadj, _, hvalid_i, hinj_q, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set N := csr.fbStart M
  set h1 := bktHash c U n_max θ.1
  have hM_pos : 0 < M := by dsimp only [M, numBucketsWhp]; positivity
  have hmono := fbStart_mono_of_adj hadj
  let keyValAt : ℕ → ℕ := fun i =>
    feistelReconstruct (bWhp n_max) h1 (csrBucketOfIdx csr.fbStart i M) (csr.qArr i)
  let rKeyAt : ℕ → ℕ := fun i =>
    if h : keyValAt i < U then fpReducedKey c U n_max θ.2 ⟨keyValAt i, h⟩ else 0
  let fpAt : ℕ → ℕ → ℕ := fun s i =>
    if hs : s < sMaxWhp c n_max then
      if hu : keyValAt i < U then fpHash c U n_max θ.2 ⟨s, hs⟩ ⟨keyValAt i, hu⟩ else 0
    else 0
  let salt1Of : ℕ → ℕ := fun b =>
    findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)
  let allSaltsFound : ℕ → Bool := Nat.rec true fun b prev => prev && (salt1Of b != 0)
  have hallSalts_iff : ∀ k, allSaltsFound k = true ↔ ∀ b < k, salt1Of b ≠ 0 := by
    intro k
    induction k with
    | zero => simp [allSaltsFound]
    | succ k ih =>
      change (allSaltsFound k && (salt1Of k != 0)) = true ↔ _
      simp only [Bool.and_eq_true, ih, bne_iff_ne]
      exact ⟨fun ⟨h1', h2'⟩ b hb => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
        · exact h1' b hlt
        · exact h2',
        fun hall => ⟨fun b hb => hall b (Nat.lt_succ_of_lt hb), hall k (Nat.lt_succ_self k)⟩⟩
  have hidx_props : ∀ i < N,
      let b := csrBucketOfIdx csr.fbStart i M
      b < M ∧ csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧
      ∃ hu : keyValAt i < U,
        feistelBucket (bWhp n_max) h1 (keyValAt i) = b ∧
        keyQuotient (bWhp n_max) (keyValAt i) = csr.qArr i ∧
        (⟨keyValAt i, hu⟩ : Fin U) ∈ Dictionary.dom dict := by
    intro i hi
    obtain ⟨hb_lt, hlo, hhi⟩ := csrBucketOfIdx_spec hfb0 hadj M le_rfl i hi
    set b := csrBucketOfIdx csr.fbStart i M
    have hp := hvalid_i b hb_lt i hlo hhi
    refine ⟨hb_lt, hlo, hhi, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    rw [Dictionary.mem_dom_iff]
    have hsome : dict ⟨keyValAt i, hp.1⟩ = some (csr.vArr i) := by
      apply ((hmap ⟨keyValAt i, hp.1⟩).2 (csr.vArr i)).mpr
      dsimp only
      rw [hp.2.1, hp.2.2.1]
      exact ⟨i, hlo, hhi, rfl, rfl⟩
    exact ⟨csr.vArr i, hsome⟩
  have hdom_to_idx : ∀ u ∈ Dictionary.dom dict,
      ∃ i < N,
        let b := feistelBucket (bWhp n_max) h1 u.val
        csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧
        csrBucketOfIdx csr.fbStart i M = b ∧ keyValAt i = u.val := by
    intro u hu
    rw [Dictionary.mem_dom_iff] at hu
    obtain ⟨v, hv_u⟩ := hu
    obtain ⟨i, hlo, hhi, hqi, _⟩ := ((hmap u).2 v).mp hv_u
    set b := feistelBucket (bWhp n_max) h1 u.val
    have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
    have hi_N : i < N := hhi.trans_le (hmono (b + 1) M (by omega) le_rfl)
    have hb_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj hb_lt hlo hhi
    refine ⟨i, hi_N, hlo, hhi, hb_eq, ?_⟩
    dsimp only [keyValAt]
    rw [hb_eq, hqi]
    exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
  have hbal_iff : checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M = true ↔
      BalancedBuckets U n_max h1 (Dictionary.dom dict) := by
    rw [checkAllBalancedCsr_iff]
    unfold BalancedBuckets BalancedBucketAt
    constructor
    · intro hall b
      have hb := (checkBalancedBucketNat_eq_true_iff hM_pos).mp (hall b.val b.isLt)
      dsimp only
      rwa [hcard_b b, hcard_dom]
    · intro hbal b hb_lt
      have hb := hbal ⟨b, hb_lt⟩
      dsimp only at hb
      rw [hcard_b ⟨b, hb_lt⟩, hcard_dom] at hb
      exact (checkBalancedBucketNat_eq_true_iff hM_pos).mpr hb
  have hinj_iff : checkPairwiseDistinctOn rKeyAt N = true ↔
      Set.InjOn (fpReducedKey c U n_max θ.2) (Dictionary.dom dict : Set (Fin U)) := by
    rw [checkPairwiseDistinctOn_iff]
    constructor
    · intro hp u₁ hu₁ u₂ hu₂ hr_eq
      rw [mem_coe] at hu₁ hu₂
      obtain ⟨i₁, hi₁, _, _, _, hk₁⟩ := hdom_to_idx u₁ hu₁
      obtain ⟨i₂, hi₂, _, _, _, hk₂⟩ := hdom_to_idx u₂ hu₂
      have hr₁ : rKeyAt i₁ = fpReducedKey c U n_max θ.2 u₁ := by
        dsimp only [rKeyAt]; simp [hk₁, u₁.isLt]
      have hr₂ : rKeyAt i₂ = fpReducedKey c U n_max θ.2 u₂ := by
        dsimp only [rKeyAt]; simp [hk₂, u₂.isLt]
      have hi_eq := hp i₁ hi₁ i₂ hi₂ (hr₁.trans (hr_eq.trans hr₂.symm))
      subst hi_eq
      exact Fin.ext (hk₁.symm.trans hk₂)
    · intro hinj_dom i₁ hi₁ i₂ hi₂ hr_eq
      obtain ⟨hb₁, hlo₁, hhi₁, hu₁_lt, hfb₁, hq₁, hmem₁⟩ := hidx_props i₁ hi₁
      obtain ⟨hb₂, hlo₂, hhi₂, hu₂_lt, hfb₂, hq₂, hmem₂⟩ := hidx_props i₂ hi₂
      have hr₁ : rKeyAt i₁ = fpReducedKey c U n_max θ.2 ⟨keyValAt i₁, hu₁_lt⟩ := by
        dsimp only [rKeyAt]; simp [hu₁_lt]
      have hr₂ : rKeyAt i₂ = fpReducedKey c U n_max θ.2 ⟨keyValAt i₂, hu₂_lt⟩ := by
        dsimp only [rKeyAt]; simp [hu₂_lt]
      have hu_eq : (⟨keyValAt i₁, hu₁_lt⟩ : Fin U) = ⟨keyValAt i₂, hu₂_lt⟩ :=
        hinj_dom hmem₁ hmem₂ (hr₁.symm.trans (hr_eq.trans hr₂))
      have hkv_eq : keyValAt i₁ = keyValAt i₂ := congrArg Fin.val hu_eq
      have hb_eq : csrBucketOfIdx csr.fbStart i₁ M = csrBucketOfIdx csr.fbStart i₂ M := by
        rw [← hfb₁, hkv_eq, hfb₂]
      have hqa_eq : csr.qArr i₁ = csr.qArr i₂ := by
        rw [← hq₁, hkv_eq, hq₂]
      rw [hb_eq] at hlo₁ hhi₁
      exact hinj_q _ hb₂ i₁ i₂ hlo₁ hhi₁ hlo₂ hhi₂ hqa_eq
  have hsalt_b_iff : ∀ b : Fin M,
      (∀ s : Fin (sMaxWhp c n_max),
        (∀ t₁ < csr.fbStart (b.val + 1) - csr.fbStart b.val,
         ∀ t₂ < csr.fbStart (b.val + 1) - csr.fbStart b.val,
          fpAt s.val (csr.fbStart b.val + t₁) = fpAt s.val (csr.fbStart b.val + t₂) → t₁ = t₂) ↔
        Set.InjOn (fpHash c U n_max θ.2 s)
          ((Dictionary.dom dict).filter (fun u =>
            feistelBucket (bWhp n_max) h1 u.val = b.val) : Set (Fin U))) := by
    intro b s
    set lo := csr.fbStart b.val
    set len := csr.fbStart (b.val + 1) - lo
    have hlo_hi : lo + len = csr.fbStart (b.val + 1) := by
      have := hadj b.val b.isLt; omega
    constructor
    · intro hpair u₁ hu₁ u₂ hu₂ hfp_eq
      rw [mem_coe, mem_filter] at hu₁ hu₂
      obtain ⟨i₁, hi₁, hlo₁, hhi₁, _, hk₁⟩ := hdom_to_idx u₁ hu₁.1
      obtain ⟨i₂, hi₂, hlo₂, hhi₂, _, hk₂⟩ := hdom_to_idx u₂ hu₂.1
      rw [hu₁.2] at hlo₁ hhi₁
      rw [hu₂.2] at hlo₂ hhi₂
      set t₁ := i₁ - lo
      set t₂ := i₂ - lo
      have ht₁_lt : t₁ < len := by omega
      have ht₂_lt : t₂ < len := by omega
      have hi₁_eq : lo + t₁ = i₁ := by omega
      have hi₂_eq : lo + t₂ = i₂ := by omega
      have hfp₁ : fpAt s.val (lo + t₁) = fpHash c U n_max θ.2 s u₁ := by
        rw [hi₁_eq]; dsimp only [fpAt]; simp [s.isLt, hk₁, u₁.isLt]
      have hfp₂ : fpAt s.val (lo + t₂) = fpHash c U n_max θ.2 s u₂ := by
        rw [hi₂_eq]; dsimp only [fpAt]; simp [s.isLt, hk₂, u₂.isLt]
      have ht_eq := hpair t₁ ht₁_lt t₂ ht₂_lt (hfp₁.trans (hfp_eq.trans hfp₂.symm))
      have hi_eq : i₁ = i₂ := by omega
      subst hi_eq
      exact Fin.ext (hk₁.symm.trans hk₂)
    · intro hinj_s t₁ ht₁ t₂ ht₂ hfp_eq
      set i₁ := lo + t₁
      set i₂ := lo + t₂
      have hi₁_hi : i₁ < csr.fbStart (b.val + 1) := by omega
      have hi₂_hi : i₂ < csr.fbStart (b.val + 1) := by omega
      have hi₁_N : i₁ < N := hi₁_hi.trans_le (hmono (b.val + 1) M (by omega) le_rfl)
      have hi₂_N : i₂ < N := hi₂_hi.trans_le (hmono (b.val + 1) M (by omega) le_rfl)
      have hb₁_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj b.isLt (by omega) hi₁_hi
      have hb₂_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj b.isLt (by omega) hi₂_hi
      obtain ⟨_, _, _, hu₁_lt, hfb₁, hq₁, hmem₁⟩ := hidx_props i₁ hi₁_N
      obtain ⟨_, _, _, hu₂_lt, hfb₂, hq₂, hmem₂⟩ := hidx_props i₂ hi₂_N
      rw [hb₁_eq] at hfb₁
      rw [hb₂_eq] at hfb₂
      have hfp₁ : fpAt s.val i₁ = fpHash c U n_max θ.2 s ⟨keyValAt i₁, hu₁_lt⟩ := by
        dsimp only [fpAt]; simp [s.isLt, hu₁_lt]
      have hfp₂ : fpAt s.val i₂ = fpHash c U n_max θ.2 s ⟨keyValAt i₂, hu₂_lt⟩ := by
        dsimp only [fpAt]; simp [s.isLt, hu₂_lt]
      have hm₁ : (⟨keyValAt i₁, hu₁_lt⟩ : Fin U) ∈
          ((Dictionary.dom dict).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :=
        mem_filter.mpr ⟨hmem₁, hfb₁⟩
      have hm₂ : (⟨keyValAt i₂, hu₂_lt⟩ : Fin U) ∈
          ((Dictionary.dom dict).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :=
        mem_filter.mpr ⟨hmem₂, hfb₂⟩
      have hu_eq := hinj_s hm₁ hm₂ (hfp₁.symm.trans (hfp_eq.trans hfp₂))
      have hkv_eq : keyValAt i₁ = keyValAt i₂ := congrArg Fin.val hu_eq
      have hqa_eq : csr.qArr i₁ = csr.qArr i₂ := by rw [← hq₁, hkv_eq, hq₂]
      have hi_eq := hinj_q b.val b.isLt i₁ i₂ (by omega) hi₁_hi (by omega) hi₂_hi hqa_eq
      omega
  dsimp only [checkGoodSeedOnState]
  change ((checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M &&
      checkPairwiseDistinctOn rKeyAt N && allSaltsFound M) = true ↔
      GoodSeedOnState c U n_max θ dict) ∧
    ((checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M &&
      checkPairwiseDistinctOn rKeyAt N && allSaltsFound M) = true → _)
  refine ⟨?_, ?_⟩
  · simp only [Bool.and_eq_true, hbal_iff, hinj_iff, hallSalts_iff, GoodSeedOnState]
    constructor
    · rintro ⟨⟨hbal, hinj_r⟩, hsalts⟩
      refine ⟨hinj_r, hbal, fun b => ?_⟩
      have hnz := hsalts b.val b.isLt
      obtain ⟨hs_lt, hpair⟩ := (findSaltInRange_props fpAt (csr.fbStart b.val)
        (csr.fbStart (b.val + 1) - csr.fbStart b.val) (sMaxWhp c n_max)).2 hnz
      exact ⟨⟨salt1Of b.val - 1, hs_lt⟩, (hsalt_b_iff b ⟨salt1Of b.val - 1, hs_lt⟩).mp hpair⟩
    · rintro ⟨hinj_r, hbal, hsalts⟩
      refine ⟨⟨hbal, hinj_r⟩, fun b hb_lt => ?_⟩
      obtain ⟨s, hinj_s⟩ := hsalts ⟨b, hb_lt⟩
      intro h0
      have hall_not := (findSaltInRange_props fpAt (csr.fbStart b)
        (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)).1.mp h0
      exact hall_not s.val s.isLt ((hsalt_b_iff ⟨b, hb_lt⟩ s).mpr hinj_s)
  · intro hok b
    simp only [Bool.and_eq_true, hallSalts_iff] at hok
    have hnz := hok.2 b.val b.isLt
    obtain ⟨hs_lt, hpair⟩ := (findSaltInRange_props fpAt (csr.fbStart b.val)
      (csr.fbStart (b.val + 1) - csr.fbStart b.val) (sMaxWhp c n_max)).2 hnz
    exact ⟨hs_lt, (hsalt_b_iff b ⟨salt1Of b.val - 1, hs_lt⟩).mp hpair⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
