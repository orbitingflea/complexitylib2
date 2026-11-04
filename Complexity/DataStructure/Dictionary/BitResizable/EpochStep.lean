/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.WindowStep
import all Complexity.DataStructure.Dictionary.BitResizable.Layout
import all Complexity.DataStructure.Dictionary.BitResizable.Companion
import all Complexity.DataStructure.Dictionary.BitResizable.InEpoch
import all Complexity.DataStructure.Dictionary.BitResizable.WindowStep
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlotStore
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctTailOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabPool
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabMove
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabDemote
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctSlabOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctChainOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctBucketOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctDeleteOps
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctValidHistory
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# In-Epoch and Epoch-Rebuild Companion Transitions

This module packages the companion witness `Companion` (`s_fix`, `td`, `dt`) and proves the
complete in-epoch `insert`/`delete` step theorems (`inEpoch_insert_step`, `inEpoch_delete_step`)
as well as the epoch-rebuild step theorem (`rebuild_step`) on the single-tape bit-resizable
dictionary.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.Companion`: companion witness `(s_fix, td, dt)` for
  `buildBitState`.
* `Cslib.DataStructure.Dictionary.BitResizable.Companion.Valid`: companion validity invariant.
* `Cslib.DataStructure.Dictionary.BitResizable.rebuildCompanion`: canonical companion state
  constructed on an epoch rebuild.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.inEpoch_insert_step`: in-epoch `insert` transition
  with `T + 1008 * c'.potential ≤ 1008 * c.potential + 2349 + 24 * epochProbeExcess`.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpoch_delete_step`: in-epoch `delete` transition
  with `T + 1008 * c'.potential ≤ 1008 * c.potential + 2529 + 24 * epochProbeExcess`.
* `Cslib.DataStructure.Dictionary.BitResizable.rebuild_step`: epoch-rebuild transition executing in
  `4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m'` instructions and
  establishing `c'.potential ≤ m'`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory Cslib.DataStructure.Memory.BitPacking
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Finset

/-! ## Section 1: Companion package and validity invariant -/

/-- Probe excess for key `u` in state `s_abs` under epoch capacity `N` and seed `θ`. -/
noncomputable abbrev epochProbeExcess (U N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (u : Fin U) : ℕ :=
  probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2 (Dynamic.dom s_abs) u

/-- Companion witness `(s_fix, td, dt)` inducing the single-tape bit-resizable state via
`buildBitState`. -/
structure Companion where
  s_fix : Memory.State
  td : ℕ → ℕ
  dt : ℕ → ℕ

/-- Slab-rebalancing potential `Φ_slot` of a companion at epoch capacity `N`. -/
def Companion.potential (U V w N : ℕ) (c : Companion) : ℕ :=
  if N = 0 then 0
  else slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem)

/-- Canonical `BitMemory.State` induced by a companion `c`. -/
noncomputable def Companion.toBitState (U V w N m : ℕ) (θ : Succinct.QuotHashSeed U N)
    (c : Companion) : BitMemory.State :=
  buildBitState U V w N m θ c.s_fix c.td c.dt

/-- Validity invariant for a companion `c` representing abstract dictionary state `s_abs` at epoch
capacity `N` and hash seed `θ`. -/
structure Companion.Valid (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (c : Companion) : Prop where
  epoch : EpochInv U N (Dynamic.dom s_abs).card
  val_bounded : Dynamic.ValuesBounded V s_abs
  fit_cap : Fits w (dictBitSize U V w N N)
  frontier_zero : c.s_fix.frontier = 0
  active : 0 < N →
    let h_space := Succinct.hashSpace U w N
    let gm := Succinct.gmAt 0 U V w N h_space c.s_fix.mem
    Succinct.DictStateInv U V w N 0 θ s_abs c.s_fix ∧
    TailDenseInv N (gm 0) (gm 1) c.td c.dt ∧
    (∀ i, c.td i < max (maxTailItems N) 1) ∧
    (∀ i, c.dt i < max (maxTailItems N) 1)

theorem EpochInv.card_le {U N m : ℕ} (h : EpochInv U N m) : m ≤ N := by
  rcases h with ⟨h0, rfl⟩ | ⟨_, hle, _, _⟩ <;> omega

theorem EpochInv.cap_le_univ {U N m : ℕ} (h : EpochInv U N m) : N ≤ U := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, _, hNU⟩
  · exact Nat.zero_le U
  · exact hNU

theorem Companion.Valid.rep {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {c : Companion}
    (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hval : c.Valid U V w N θ s_abs) :
    Rep U V w N θ s_abs (c.toBitState U V w N (Dynamic.dom s_abs).card θ) := by
  let m := (Dynamic.dom s_abs).card
  have hm_le_N : m ≤ N := hval.epoch.card_le
  have hN_le_U : N ≤ U := hval.epoch.cap_le_univ
  have hsz_le : dictBitSize U V w N m ≤ dictBitSize U V w N N := by
    unfold dictBitSize; exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hm_le_N) _
  have hfit_sz : Fits w (dictBitSize U V w N m) := hval.fit_cap.of_le hsz_le
  have hfit_N : Fits w N := hU.of_le hN_le_U
  have hfit_m : Fits w m := hfit_N.of_le hm_le_N
  have hfit_meta : Fits w (epochMetaBits U w N) :=
    hval.fit_cap.of_le (by unfold dictBitSize; omega)
  have hfit_item : Fits w (itemBits U V N) := by
    rcases Nat.eq_zero_or_pos N with rfl | hN_pos
    · have hq : quotientBits U 0 ≤ w := quotientBits_le_of_le_pow hU.le
      have hv : valBits V ≤ w := valBits_le_of_le_pow hV
      have hd0 : dictBitSize U V w 0 0 = 4 * w := by
        unfold dictBitSize epochMetaBits epochMetaWords; simp
      exact hval.fit_cap.of_le (by unfold itemBits; omega)
    · exact hval.fit_cap.of_le (by
        unfold dictBitSize
        have : 1 * itemBits U V N ≤ N * itemBits U V N := Nat.mul_le_mul_right _ hN_pos
        omega)
  refine rep_buildBitState hw hU hV θ hval.epoch hval.val_bounded c.s_fix c.td c.dt
    ⟨hfit_m, hfit_N, hfit_item, hfit_meta, hfit_sz⟩ (fun hN_pos => ?_)
  obtain ⟨hdict, htd, htd_b, hdt_b⟩ := hval.active hN_pos
  obtain ⟨_, _, hfit_hash⟩ := dictEnv_of_fits_dictBitSize hw hN_pos hN_le_U hU hV hval.fit_cap
  obtain ⟨L, hb_inv⟩ := hdict.hbucket
  have hntails_le : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem 1 ≤
      maxTailItems N := by
    by_cases hb0 : bucketBits N = 0
    · have hM0 : maxTailItems N = 0 := by simp [maxTailItems, tailCapPerBucket, hb0]
      rw [hM0]
      by_contra hpos
      have := htd.td_lt 0 (by omega)
      omega
    · exact (hb_inv.hslot.multi_tail (Nat.pos_of_ne_zero hb0)).ntails_le
  have hM_le_pow : max (maxTailItems N) 1 ≤ 2 ^ globalPtrBits N := by
    have hM_le_N : maxTailItems N ≤ N := maxTailItems_le N
    have hN_lt : N < 2 ^ globalPtrBits N :=
      Succinct.lt_two_pow_globalPtrBits_of_le_n_max le_rfl
    omega
  exact ⟨hfit_hash, hdict, hntails_le, htd,
    fun t _ => lt_of_lt_of_le (htd_b t) hM_le_pow,
    fun idx _ => lt_of_lt_of_le (hdt_b idx) hM_le_pow⟩

/-! ## Section 2: In-epoch `insert` and `delete` companion step theorems -/

/-- **In-epoch `insert` companion step (`inEpoch_insert_step`):**
when the post-insert key count remains in the current epoch (`EpochInv U N m'`, `0 < N`),
`inEpochSyncCode` updates the single-tape bit-resizable state in `T` instructions under demonic
`.grow`, where
`T + 1008 * c'.potential U V w N ≤ 1008 * c.potential U V w N + 2349 + 24 * epochProbeExcess`. -/
theorem inEpoch_insert_step {U V w N : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    (hval_c : c.Valid U V w N θ s_abs) (hN : 0 < N)
    (u : Fin U) (v : ℕ) (hv : v < V)
    (hepoch' : EpochInv U N (Dynamic.dom (Function.update s_abs u (some v))).card)
    {x : BitRAM.Data 12} (hx_wf : x.WellFormed w)
    (hx_eq : x.toBitMemoryState = c.toBitState U V w N (Dynamic.dom s_abs).card θ) :
    let s_abs' := Function.update s_abs u (some v)
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    ∃ (c' : Companion) (T : ℕ),
      c'.Valid U V w N θ s_abs' ∧
      BitRAM.DemonicExecWithin w
        (inEpochSyncCode U V w N m m' x.toBitMemoryState (c'.toBitState U V w N m' θ)) x
        (fun y => y.toBitMemoryState = c'.toBitState U V w N m' θ ∧ y.WellFormed w) T ∧
      T + 1008 * c'.potential U V w N ≤
        1008 * c.potential U V w N + 2349 +
          24 * epochProbeExcess U N θ s_abs u := by
  intro s_abs' m m'
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hN_le_U : N ≤ U := hval_c.epoch.cap_le_univ
  obtain ⟨hwf, henv, _⟩ := dictEnv_of_fits_dictBitSize hw hN hN_le_U hU hV hval_c.fit_cap
  obtain ⟨hdict, htd, htd_b, hdt_b⟩ := hval_c.active hN
  obtain ⟨_, hb_inv⟩ := hdict.hbucket
  have hm'_le_N : m' ≤ N := hepoch'.card_le
  have hvalid_op : (Dynamic.spec U V N).valid s_abs (.insert u v) := by
    refine ⟨?_, hv⟩
    by_cases hsome : (s_abs u).isSome
    · exact Or.inr hsome
    · left
      have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      have hcard := Dictionary.card_dom_insert_eq_of_eq_none hnone v
      change (Dynamic.dom s_abs').card = m + 1 at hcard
      omega
  obtain ⟨_hpre, hfr_eq, _hout, hdict', hcost_le⟩ :=
    Succinct.insertWithHashProg_dict_spec hwf henv θ hdict u v hvalid_op
  let h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
  let prog := Succinct.insertWithHashProg U V w N (((0, u.val), v), h_q)
  let s_fix' := (Memory.spec 0).clientState c.s_fix prog
  have hm0_le : min m m' ≤ (Dynamic.dom s_abs).card := Nat.min_le_left m m'
  have hm0_tot : min m m' ≤
      Succinct.totalSlots N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) := by
    rw [hdict.htot]; exact hm0_le
  let L_p := (List.range (min m m')).map
    (physOfDense N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) c.dt)
  let L_m := List.range (epochMetaWords U w N)
  have hnodup_p : L_p.Nodup := nodup_map_physOfDense hb_inv.hslot htd hm0_tot
  obtain ⟨td', dt', W, hpost⟩ :=
    insertWithHashProg_window (L_p := L_p) (L_m := L_m)
      hnodup_p List.nodup_range hwf henv θ hdict u v hvalid_op hm0_le
      c.td c.dt htd htd_b hdt_b
  let c' : Companion := ⟨s_fix', td', dt'⟩
  have hval_s' : Dynamic.ValuesBounded V s_abs' := by
    intro k w_val hkw
    dsimp only [s_abs'] at hkw
    by_cases hku : k = u
    · subst hku; rw [Function.update_self] at hkw; injection hkw with hvw; subst hvw; exact hv
    · rw [Function.update_of_ne hku] at hkw; exact hval_c.val_bounded k w_val hkw
  have hval_c' : c'.Valid U V w N θ s_abs' :=
    ⟨hepoch', hval_s', hval_c.fit_cap,
      hfr_eq.trans hval_c.frontier_zero,
      fun _ => ⟨hdict', hpost.tailDense, hpost.td_lt, hpost.dt_lt⟩⟩
  have hrep' := hval_c'.rep hw hU hV
  have htar_wf : (c'.toBitState U V w N m' θ).WellFormed w := hrep'.wellFormed
  have hx_sz : x.bitSize = dictBitSize U V w N m := by
    change x.toBitMemoryState.bitSize = _; rw [hx_eq]; rfl
  have htar_sz : (c'.toBitState U V w N m' θ).bitSize = dictBitSize U V w N m' := rfl
  have hm_cases : m' = m + 1 ∨ m = m' + 1 ∨ m' = m := by
    by_cases hsome : (s_abs u).isSome
    · right; right; exact Dictionary.card_dom_insert_eq_of_isSome hsome v
    · left
      have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      exact Dictionary.card_dom_insert_eq_of_eq_none hnone v
  have hexec := inEpochSyncCode_exec (c'.toBitState U V w N m' θ)
    hw hU.le hV hx_wf htar_wf hx_sz htar_sz hm_cases
  refine ⟨c', _, hval_c', hexec, ?_⟩
  rw [hx_eq]
  have hd_dense := changedDenseList_length_le (U := U) (V := V) (w := w) (N := N)
    (m := m) (m' := m') hw hU.le hV θ c.s_fix s_fix' c.td c.dt td' dt'
  have hd_meta := changedMetaList_length_le (U := U) (V := V) (w := w) (N := N)
    (m := m) (m' := m') hw hN θ prog c.s_fix hfr_eq c.td c.dt td' dt'
  have hpot_c : c.potential U V w N =
      slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) := by
    unfold Companion.potential; rw [ite_eq_right hN0]
  have hpot_c' : c'.potential U V w N =
      slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix'.mem) := by
    unfold Companion.potential; rw [ite_eq_right hN0]
  rw [hpot_c, hpot_c']
  have h1 := hpost.pot_le
  have h2 := hpost.diff_qv
  have h3 := hpost.diff_phys
  have h4 := hpost.diff_td
  have h5 := hpost.diff_dt
  dsimp only [Companion.toBitState, c', L_p, L_m, prog, h_q, s_fix', m, epochProbeExcess]
    at hd_dense hd_meta hcost_le h1 h2 h3 h4 h5 ⊢
  omega

/-- **In-epoch `delete` companion step (`inEpoch_delete_step`):**
when the post-delete key count remains in the current epoch (`EpochInv U N m'`, `0 < N`),
`inEpochSyncCode` updates the single-tape bit-resizable state in `T` instructions under demonic
`.grow`, where
`T + 1008 * c'.potential U V w N ≤ 1008 * c.potential U V w N + 2529 + 24 * epochProbeExcess`. -/
theorem inEpoch_delete_step {U V w N : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    (hval_c : c.Valid U V w N θ s_abs) (hN : 0 < N)
    (u : Fin U)
    (hepoch' : EpochInv U N (Dynamic.dom (Function.update s_abs u none)).card)
    {x : BitRAM.Data 12} (hx_wf : x.WellFormed w)
    (hx_eq : x.toBitMemoryState = c.toBitState U V w N (Dynamic.dom s_abs).card θ) :
    let s_abs' := Function.update s_abs u none
    let m := (Dynamic.dom s_abs).card
    let m' := (Dynamic.dom s_abs').card
    ∃ (c' : Companion) (T : ℕ),
      c'.Valid U V w N θ s_abs' ∧
      BitRAM.DemonicExecWithin w
        (inEpochSyncCode U V w N m m' x.toBitMemoryState (c'.toBitState U V w N m' θ)) x
        (fun y => y.toBitMemoryState = c'.toBitState U V w N m' θ ∧ y.WellFormed w) T ∧
      T + 1008 * c'.potential U V w N ≤
        1008 * c.potential U V w N + 2529 +
          24 * epochProbeExcess U N θ s_abs u := by
  intro s_abs' m m'
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN
  have hN_le_U : N ≤ U := hval_c.epoch.cap_le_univ
  obtain ⟨hwf, henv, _⟩ := dictEnv_of_fits_dictBitSize hw hN hN_le_U hU hV hval_c.fit_cap
  obtain ⟨hdict, htd, htd_b, hdt_b⟩ := hval_c.active hN
  obtain ⟨_, hb_inv⟩ := hdict.hbucket
  obtain ⟨found, j_del, phys_del, q_last, hprep_res, _hpre_p, _hst_p, _hq_lt, _hpre_f,
    hfr_eq, _hout, hdict', hcost_le⟩ :=
    Succinct.deleteWithHashProg_dict_spec hwf henv θ hdict u
  let h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
  let h_q_last := Succinct.hValOfSeed U N θ q_last
  let d_fin := ((((0, u.val), h_q), ((found, j_del), phys_del)), h_q_last)
  let prog_fin := Succinct.deleteFinishWithHashProg U V w N d_fin
  let s_fix' := (Memory.spec 0).clientState c.s_fix prog_fin
  have hm0_le : min m m' ≤ (Dynamic.dom s_abs').card := Nat.min_le_right m m'
  have hm0_tot : min m m' ≤
      Succinct.totalSlots N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) := by
    rw [hdict.htot]; exact Nat.min_le_left m m'
  let L_p := (List.range (min m m')).map
    (physOfDense N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) c.dt)
  let L_m := List.range (epochMetaWords U w N)
  have hnodup_p : L_p.Nodup := nodup_map_physOfDense hb_inv.hslot htd hm0_tot
  obtain ⟨td', dt', W, hpost⟩ :=
    deleteFinishWithHashProg_window (L_p := L_p) (L_m := L_m)
      hnodup_p List.nodup_range hwf henv θ hdict u hm0_le
      c.td c.dt htd htd_b hdt_b
  rw [hprep_res] at hpost
  let c' : Companion := ⟨s_fix', td', dt'⟩
  have hval_s' : Dynamic.ValuesBounded V s_abs' := by
    intro k w_val hkw
    dsimp only [s_abs'] at hkw
    by_cases hku : k = u
    · subst hku; simp at hkw
    · rw [Function.update_of_ne hku] at hkw; exact hval_c.val_bounded k w_val hkw
  have hval_c' : c'.Valid U V w N θ s_abs' :=
    ⟨hepoch', hval_s', hval_c.fit_cap,
      hfr_eq.trans hval_c.frontier_zero,
      fun _ => ⟨hdict', hpost.tailDense, hpost.td_lt, hpost.dt_lt⟩⟩
  have hrep' := hval_c'.rep hw hU hV
  have htar_wf : (c'.toBitState U V w N m' θ).WellFormed w := hrep'.wellFormed
  have hx_sz : x.bitSize = dictBitSize U V w N m := by
    change x.toBitMemoryState.bitSize = _; rw [hx_eq]; rfl
  have htar_sz : (c'.toBitState U V w N m' θ).bitSize = dictBitSize U V w N m' := rfl
  have hm_cases : m' = m + 1 ∨ m = m' + 1 ∨ m' = m := by
    by_cases hsome : (s_abs u).isSome
    · right; left
      have hpos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
      have hdel := Dynamic.card_dom_delete_eq_of_isSome hsome
      change m' = m - 1 at hdel
      omega
    · right; right
      have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hsome
      exact Dynamic.card_dom_delete_eq_of_eq_none hnone
  have hexec := inEpochSyncCode_exec (c'.toBitState U V w N m' θ)
    hw hU.le hV hx_wf htar_wf hx_sz htar_sz hm_cases
  refine ⟨c', _, hval_c', hexec, ?_⟩
  rw [hx_eq]
  have hd_dense := changedDenseList_length_le (U := U) (V := V) (w := w) (N := N)
    (m := m) (m' := m') hw hU.le hV θ c.s_fix s_fix' c.td c.dt td' dt'
  have hd_meta := changedMetaList_length_le (U := U) (V := V) (w := w) (N := N)
    (m := m) (m' := m') hw hN θ prog_fin c.s_fix hfr_eq c.td c.dt td' dt'
  have hpot_c : c.potential U V w N =
      slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) c.s_fix.mem) := by
    unfold Companion.potential; rw [ite_eq_right hN0]
  have hpot_c' : c'.potential U V w N =
      slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix'.mem) := by
    unfold Companion.potential; rw [ite_eq_right hN0]
  rw [hpot_c, hpot_c']
  have h1 := hpost.pot_le
  have h2 := hpost.diff_qv
  have h3 := hpost.diff_phys
  have h4 := hpost.diff_td
  have h5 := hpost.diff_dt
  dsimp only [Companion.toBitState, c', L_p, L_m, prog_fin, d_fin, h_q_last, h_q,
    s_fix', m, epochProbeExcess] at hd_dense hd_meta hcost_le h1 h2 h3 h4 h5 ⊢
  omega

/-! ## Section 3: Canonical companion construction and epoch rebuild (`rebuild_step`) -/

/-- For any abstract state `s_abs` with `(Dynamic.dom s_abs).card ≤ N`, values bounded by `V`,
and valid parameters, there exists a companion state `(s_fix, td, dt)` with `s_fix.frontier = 0`,
`Succinct.DictStateInv`, `TailDenseInv`, and `slotPotential ≤ (Dynamic.dom s_abs).card`. -/
theorem exists_active_companion_of_card_le {U V w N : ℕ}
    (hwf : Succinct.DictParamsWf U V w N)
    (henv : Succinct.DictEnv U V w N (Succinct.hashSpace U w N) w 0)
    (θ : Succinct.QuotHashSeed U N) :
    ∀ (D : Finset (Fin U)) (s_abs : Dynamic.State U),
      Dynamic.dom s_abs = D →
      D.card ≤ N →
      Dynamic.ValuesBounded V s_abs →
      ∃ (s_fix : Memory.State) (td dt : ℕ → ℕ),
        let gm := Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
        s_fix.frontier = 0 ∧
        Succinct.DictStateInv U V w N 0 θ s_abs s_fix ∧
        TailDenseInv N (gm 0) (gm 1) td dt ∧
        (∀ i, td i < max (maxTailItems N) 1) ∧
        (∀ i, dt i < max (maxTailItems N) 1) ∧
        slotPotential N gm ≤ D.card := by
  intro D
  induction D using Finset.induction_on with
  | empty =>
    intro s_abs hdom _ _
    have hs_empty : s_abs = Dynamic.empty U := by
      funext u
      have hu : u ∉ Dynamic.dom s_abs := by rw [hdom]; simp
      exact notMem_dom_iff.mp hu
    subst hs_empty
    let zState : Memory.State := ⟨fun _ => 0, 0⟩
    have hgm0 : ∀ i, Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) zState.mem i = 0 := by
      intro i; unfold Succinct.gmAt readPacked; split_ifs <;> simp [zState]
    have hlm0 : ∀ p, Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) zState.mem p = 0 := by
      intro p; unfold Succinct.lmAt readPacked; split_ifs <;> simp [zState]
    obtain ⟨hinv0, hpot0⟩ := Succinct.dictStateInv_of_zero (U := U) (V := V) (w₀ := w)
      (n_max := N) (base := 0) θ (s := zState) hgm0 hlm0
    refine ⟨zState, fun _ => 0, fun _ => 0, rfl, hinv0, ?_,
      fun _ => lt_max_of_lt_right Nat.one_pos,
      fun _ => lt_max_of_lt_right Nat.one_pos,
      by rw [hpot0]; exact Nat.zero_le _⟩
    have h1 : Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) zState.mem 1 = 0 := hgm0 1
    exact ⟨fun t ht => by rw [h1] at ht; omega,
      fun t ht => by rw [h1] at ht; omega,
      fun t ht => by rw [h1] at ht; omega,
      fun d hlo hhi => by rw [h1] at hhi; omega⟩
  | @insert u D hu ih =>
    intro s_abs hdom hcard hval
    let s_prev := Function.update s_abs u none
    have hdom_prev : Dynamic.dom s_prev = D := by
      ext x
      rw [mem_dom_iff_isSome]
      dsimp only [s_prev]
      by_cases hxu : x = u
      · subst hxu; simp [hu]
      · rw [Function.update_of_ne hxu, ← mem_dom_iff_isSome]
        change x ∈ Dynamic.dom s_abs ↔ x ∈ D
        rw [hdom]
        simp [hxu]
    have hcard_ins : (insert u D).card = D.card + 1 := Finset.card_insert_of_notMem hu
    have hcard_prev : D.card ≤ N := by omega
    have hval_prev : Dynamic.ValuesBounded V s_prev := by
      intro k w_val hkw
      dsimp only [s_prev] at hkw
      by_cases hku : k = u
      · subst hku; simp at hkw
      · rw [Function.update_of_ne hku] at hkw; exact hval k w_val hkw
    obtain ⟨s₀, td₀, dt₀, hfr₀, hinv₀, htd₀, htd_b₀, hdt_b₀, hpot₀⟩ :=
      ih s_prev hdom_prev hcard_prev hval_prev
    have hu_dom : u ∈ Dynamic.dom s_abs := by rw [hdom]; exact Finset.mem_insert_self u D
    obtain ⟨v, hv_eq⟩ := mem_dom_iff.mp hu_dom
    have hv_lt : v < V := hval u v hv_eq
    have hvalid_ins : (Dynamic.spec U V N).valid s_prev (.insert u v) := by
      refine ⟨Or.inl ?_, hv_lt⟩
      rw [hdom_prev]; omega
    obtain ⟨_hpre, hfr₁, _hout, hinv₁, _hcost⟩ :=
      Succinct.insertWithHashProg_dict_spec hwf henv θ hinv₀ u v hvalid_ins
    obtain ⟨td', dt', W, hpost⟩ :=
      insertWithHashProg_window (m₀ := 0) (L_p := []) (L_m := [])
        List.nodup_nil List.nodup_nil hwf henv θ hinv₀ u v hvalid_ins (Nat.zero_le _)
        td₀ dt₀ htd₀ htd_b₀ hdt_b₀
    have hs_eq : Function.update s_prev u (some v) = s_abs := by
      funext x
      by_cases hxu : x = u
      · subst hxu; simp [hv_eq]
      · simp [s_prev, hxu]
    rw [hs_eq] at hinv₁
    have hpot_step := hpost.pot_le
    dsimp only at hpot_step
    refine ⟨_, td', dt', hfr₁.trans hfr₀, hinv₁, hpost.tailDense, hpost.td_lt, hpost.dt_lt, ?_⟩
    rw [hcard_ins]; omega

theorem exists_companion_of_epoch {U V w N' : ℕ}
    (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ' : Succinct.QuotHashSeed U N') (s_abs' : Dynamic.State U)
    (hepoch' : EpochInv U N' (Dynamic.dom s_abs').card)
    (hval' : Dynamic.ValuesBounded V s_abs')
    (hfit' : Fits w (dictBitSize U V w N' N')) :
    ∃ c' : Companion,
      c'.Valid U V w N' θ' s_abs' ∧
      c'.potential U V w N' ≤ (Dynamic.dom s_abs').card := by
  rcases Nat.eq_zero_or_pos N' with rfl | hN'
  · refine ⟨⟨⟨fun _ => 0, 0⟩, fun _ => 0, fun _ => 0⟩,
      ⟨hepoch', hval', hfit', rfl, fun hpos => by omega⟩, ?_⟩
    unfold Companion.potential
    simp
  · have hN'0 : N' ≠ 0 := Nat.ne_of_gt hN'
    have hNU : N' ≤ U := hepoch'.cap_le_univ
    obtain ⟨hwf, henv, _⟩ := dictEnv_of_fits_dictBitSize hw hN' hNU hU hV hfit'
    obtain ⟨s_fix, td, dt, hfr, hdict, htd, htd_b, hdt_b, hpot⟩ :=
      exists_active_companion_of_card_le hwf henv θ' (Dynamic.dom s_abs') s_abs'
        rfl hepoch'.card_le hval'
    refine ⟨⟨s_fix, td, dt⟩, ⟨hepoch', hval', hfit', hfr, fun _ => ⟨hdict, htd, htd_b, hdt_b⟩⟩, ?_⟩
    unfold Companion.potential
    rw [ite_eq_right hN'0]
    exact hpot

/-- Canonical companion state constructed on an epoch rebuild to capacity `N'` and seed `θ'`. -/
noncomputable def rebuildCompanion (U V w N' : ℕ) (θ' : Succinct.QuotHashSeed U N')
    (s_abs' : Dynamic.State U)
    (hepoch' : EpochInv U N' (Dynamic.dom s_abs').card)
    (hval' : Dynamic.ValuesBounded V s_abs')
    (hfit' : Fits w (dictBitSize U V w N' N'))
    (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w) : Companion :=
  Classical.choose (exists_companion_of_epoch hw hU hV θ' s_abs' hepoch' hval' hfit')

theorem rebuildCompanion_valid {U V w N' : ℕ} (θ' : Succinct.QuotHashSeed U N')
    (s_abs' : Dynamic.State U)
    (hepoch' : EpochInv U N' (Dynamic.dom s_abs').card)
    (hval' : Dynamic.ValuesBounded V s_abs')
    (hfit' : Fits w (dictBitSize U V w N' N'))
    (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w) :
    let c' := rebuildCompanion U V w N' θ' s_abs' hepoch' hval' hfit' hw hU hV
    c'.Valid U V w N' θ' s_abs' ∧
    c'.potential U V w N' ≤ (Dynamic.dom s_abs').card :=
  Classical.choose_spec (exists_companion_of_epoch hw hU hV θ' s_abs' hepoch' hval' hfit')

/-- **Epoch-rebuild companion step (`rebuild_step`):**
rebuilds the single-tape bit-resizable dictionary from `(N, m)` to new epoch capacity `N'` and
hash seed `θ'` in
`4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * (Dynamic.dom s_abs').card`
instructions under demonic `.grow`, producing a valid companion `c'` with
`c'.potential U V w N' ≤ (Dynamic.dom s_abs').card`. -/
theorem rebuild_step {U V w N m N' : ℕ} (hw : 0 < w) (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ' : Succinct.QuotHashSeed U N') (s_abs' : Dynamic.State U)
    (hepoch' : EpochInv U N' (Dynamic.dom s_abs').card)
    (hval' : Dynamic.ValuesBounded V s_abs')
    (hfit' : Fits w (dictBitSize U V w N' N'))
    {x : BitRAM.Data 12} (hx_wf : x.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N m) :
    let m' := (Dynamic.dom s_abs').card
    let c' := rebuildCompanion U V w N' θ' s_abs' hepoch' hval' hfit' hw hU hV
    c'.Valid U V w N' θ' s_abs' ∧
    c'.potential U V w N' ≤ m' ∧
    BitRAM.DemonicExecWithin w
      (rebuildSyncCode U V w N m N' m' (c'.toBitState U V w N' m' θ')) x
      (fun y => y.toBitMemoryState = c'.toBitState U V w N' m' θ' ∧ y.WellFormed w)
      (4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m') := by
  intro m' c'
  obtain ⟨hval_c', hpot_c'⟩ := rebuildCompanion_valid θ' s_abs' hepoch' hval' hfit' hw hU hV
  have hrep' := hval_c'.rep hw hU hV
  have htar_wf : (c'.toBitState U V w N' m' θ').WellFormed w := hrep'.wellFormed
  have hexec := rebuildSyncCode_exec (N := N) (c'.toBitState U V w N' m' θ')
    hw hU.le hV hx_wf htar_wf hx_sz rfl
  exact ⟨hval_c', hpot_c', hexec⟩

end Cslib.DataStructure.Dictionary.BitResizable
