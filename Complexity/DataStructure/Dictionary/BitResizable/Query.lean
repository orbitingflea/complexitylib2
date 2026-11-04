/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Operations

/-!
# Concrete `BitRAM` Query and In-Place Update Programs

This module builds on `Complexity.DataStructure.Dictionary.BitResizable.Operations` to provide:
1. Concrete `BitRAM.Code .standard 12` programs for dictionary queries (`probeDenseListCode`,
   `queryCode`) with worst-case (`111 + 37 * pe`) and expected (`≤ 296`) instruction bounds.
2. Concrete `BitRAM.Code .standard 12` program for in-place updates of existing keys
   (`insertHitCode`) in `≤ 201 + 37 * pe` instructions (`≤ 386` expected), preserving `bitSize`,
   metadata words, and `potential`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Concrete `BitRAM.Code` for `query` (`probeDenseListCode` and `queryCode`) -/

/-- Probe a list `ds : List ℕ` of dense item indices `d < n_t` for target quotient `q_target`.
If found at `d ∈ ds`, sets `r1 = 1` (`some`), `r0 = denseValAt ... d`, and `r2 = d`; otherwise
sets `r1 = 0` (`none`). -/
@[expose]
def probeDenseListCode (U V w N q_target : ℕ) : List ℕ → BitRAM.Code .standard 12
  | [] => .op (.const 1 0)
  | d :: ds =>
    .seq (readFieldCode (itemQuotBitOff U V w N d) (quotientBits U N))
      (.seq (.op (.const 9 q_target))
        (.branch (.eq 0 9)
          (.seq (readFieldCode (itemValBitOff U V w N d) (valBits V))
            (.seq (.op (.const 1 1))
              (.op (.const 2 d))))
          (probeDenseListCode U V w N q_target ds)))

/-- Execution certificate for `probeDenseListCode`: executes in at most `37 + 37 * ds.length`
`BitRAM` instructions, preserving `toBitMemoryState` and `WellFormed w`. -/
theorem probeDenseListCode_exec {U V w N n_t q_target : ℕ} (ds : List ℕ)
    {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hn_t : n_t < 2 ^ w)
    (hx : x.WellFormed w)
    (hds : ∀ d ∈ ds, d < n_t)
    (hsz : dictBitSize U V w N n_t ≤ x.bitSize)
    (hq_fits : Fits w q_target) :
    BitRAM.DemonicExecWithin w (probeDenseListCode U V w N q_target ds) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        (if ∃ d ∈ ds, denseQuotAt U V w N x.toBitMemoryState d = q_target then
          y.regs 1 = 1 ∧
          y.regs 2 =
            ((ds.find? (fun d => decide (denseQuotAt U V w N x.toBitMemoryState d = q_target))).getD
              0) ∧
          y.regs 2 ∈ ds ∧
          denseQuotAt U V w N x.toBitMemoryState (y.regs 2) = q_target ∧
          y.regs 0 = denseValAt U V w N x.toBitMemoryState (y.regs 2)
        else
          y.regs 1 = 0))
      (37 + 37 * ds.length) := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  induction ds generalizing x with
  | nil =>
    have h0 : Fits w 0 := fits_zero w
    refine (DemonicExecWithin.const h0 ?_).mono (fun y hy => hy) (by omega)
    have hy_wf : (x.set 1 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi1 : i = 1
      · subst hi1; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi1]
        exact hx.regs_fits i
    exact ⟨rfl, hy_wf, rfl⟩
  | cons d ds' ih =>
    have hd_lt : d < n_t := hds d List.mem_cons_self
    have hds' : ∀ d' ∈ ds', d' < n_t := fun d' hd' => hds d' (List.mem_cons_of_mem d hd')
    have h1_fits : Fits w 1 := fits_one (Nat.ne_of_gt hw)
    have hd_fits : Fits w d := lt_trans hd_lt hn_t
    have hd_end : itemBitOff U V w N (d + 1) ≤ x.bitSize := by
      have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd_lt
      simp only [itemBitOff, dictBitSize] at hsz ⊢
      omega
    have hq_end : itemQuotBitOff U V w N d + quotientBits U N ≤ x.bitSize := by
      rw [itemBitOff_succ] at hd_end
      simp only [itemQuotBitOff, itemBits] at hd_end ⊢
      omega
    have hv_end : itemValBitOff U V w N d + valBits V ≤ x.bitSize := by
      rwa [itemValBitOff_add_valBits]
    refine .seq (T₁ := 34) (T₂ := 39 + 37 * ds'.length + 1)
      (readFieldCode_exec hw hx hqw hq_end)
      (fun y₁ ⟨hr0_q, hst₁, hy₁_wf⟩ => ?_)
      (by simp only [List.length_cons]; omega)
    refine DemonicExecWithin.step_const (T := 39 + 37 * ds'.length) hq_fits ?_
    let x₂ : BitRAM.Data 12 := y₁.set 9 q_target
    have hx₂_wf : x₂.WellFormed w := by
      refine ⟨fun i => ?_, hy₁_wf.mem_wf⟩
      by_cases hi9 : i = 9
      · subst hi9; exact hq_fits
      · simp only [x₂, BitRAM.Data.set, Function.update_of_ne hi9]
        exact hy₁_wf.regs_fits i
    by_cases heq : denseQuotAt U V w N x.toBitMemoryState d = q_target
    · have hcond : BitRAM.CondHolds (.eq 0 9) x₂ := by
        change x₂.regs 0 = x₂.regs 9
        dsimp only [x₂, BitRAM.Data.set]
        rw [Function.update_of_ne (by decide), Function.update_self, hr0_q]
        exact heq
      have hv_end₂ : itemValBitOff U V w N d + valBits V ≤ x₂.bitSize := by
        change itemValBitOff U V w N d + valBits V ≤ y₁.toBitMemoryState.bitSize
        rw [hst₁]
        exact hv_end
      refine .branch_pos (T₀ := 36) hcond ?_ (by omega)
      refine .seq (T₁ := 34) (T₂ := 2)
        (readFieldCode_exec hw hx₂_wf hvw hv_end₂)
        (fun y₂ ⟨hr0_v, hst₂, hy₂_wf⟩ => ?_) (by omega)
      refine DemonicExecWithin.step_const (T := 1) h1_fits ?_
      refine DemonicExecWithin.const hd_fits ?_
      let y := (y₂.set 1 1).set 2 d
      have hy_wf : y.WellFormed w := by
        refine ⟨fun i => ?_, hy₂_wf.mem_wf⟩
        by_cases hi2 : i = 2
        · subst hi2; exact hd_fits
        · by_cases hi1 : i = 1
          · subst hi1; exact h1_fits
          · simp only [y, BitRAM.Data.set, Function.update_of_ne hi2, Function.update_of_ne hi1]
            exact hy₂_wf.regs_fits i
      have hy_st : y.toBitMemoryState = x.toBitMemoryState := hst₂.trans hst₁
      have hex : ∃ d' ∈ d :: ds', denseQuotAt U V w N x.toBitMemoryState d' = q_target :=
        ⟨d, List.mem_cons_self, heq⟩
      refine ⟨hy_st, hy_wf, ?_⟩
      rw [ite_eq_left hex]
      have hfind :
          ((d :: ds').find? (fun d =>
            decide (denseQuotAt U V w N x.toBitMemoryState d = q_target))).getD 0 = d := by
        simp only [List.find?_cons, heq, decide_true, Option.getD_some]
      have hr0_eq : y.regs 0 = denseValAt U V w N x.toBitMemoryState d := by
        calc y.regs 0 = y₂.regs 0 := rfl
          _ = x₂.toBitMemoryState.getField w (itemValBitOff U V w N d) (valBits V) := hr0_v
          _ = denseValAt U V w N x.toBitMemoryState d := by
            change y₁.toBitMemoryState.getField w _ _ = _
            rw [hst₁]; rfl
      exact ⟨rfl, hfind.symm, List.mem_cons_self, heq, hr0_eq⟩
    · have hcond : ¬BitRAM.CondHolds (.eq 0 9) x₂ := by
        change x₂.regs 0 ≠ x₂.regs 9
        dsimp only [x₂, BitRAM.Data.set]
        rw [Function.update_of_ne (by decide), Function.update_self, hr0_q]
        exact heq
      have hsz₂ : dictBitSize U V w N n_t ≤ x₂.bitSize := by
        change dictBitSize U V w N n_t ≤ y₁.toBitMemoryState.bitSize
        rw [hst₁]
        exact hsz
      refine .branch_neg (T₀ := 37 + 37 * ds'.length) hcond ?_ (by omega)
      refine (ih hx₂_wf hds' hsz₂).mono (fun y ⟨hst₂, hy_wf, hres⟩ => ?_) le_rfl
      have hy_st : y.toBitMemoryState = x.toBitMemoryState := hst₂.trans hst₁
      have hx₂_st : x₂.toBitMemoryState = x.toBitMemoryState := hst₁
      rw [hx₂_st] at hres
      refine ⟨hy_st, hy_wf, ?_⟩
      by_cases hex' : ∃ d' ∈ ds', denseQuotAt U V w N x.toBitMemoryState d' = q_target
      · rw [ite_eq_left hex'] at hres
        have hex : ∃ d' ∈ d :: ds', denseQuotAt U V w N x.toBitMemoryState d' = q_target :=
          let ⟨d', hd', hq'⟩ := hex'
          ⟨d', List.mem_cons_of_mem d hd', hq'⟩
        rw [ite_eq_left hex]
        have hfind :
            ((d :: ds').find?
              (fun d => decide (denseQuotAt U V w N x.toBitMemoryState d = q_target))).getD 0 =
            (ds'.find?
              (fun d => decide (denseQuotAt U V w N x.toBitMemoryState d = q_target))).getD 0 := by
          simp only [List.find?_cons, heq, decide_false]
        exact ⟨hres.1, hres.2.1.trans hfind.symm, List.mem_cons_of_mem d hres.2.2.1,
          hres.2.2.2.1, hres.2.2.2.2⟩
      · rw [ite_eq_right hex'] at hres
        have hnot : ¬∃ d' ∈ d :: ds', denseQuotAt U V w N x.toBitMemoryState d' = q_target := by
          rintro ⟨d', hd', hq'⟩
          rcases List.mem_cons.mp hd' with rfl | hmem'
          · exact heq hq'
          · exact hex' ⟨d', hmem', hq'⟩
        rw [ite_eq_right hnot]
        exact hres

/-- Logical bucket slots probed for `(b, m)`: the indexed micro-chain `L b m` followed by any
overflow slots `effBucketCap N ≤ j < Succinct.bCount N gm b`. -/
@[expose]
def bucketProbeSlots (N : ℕ) (gm : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (b m : ℕ) : List ℕ :=
  L b m ++ (List.range (Succinct.bCount N gm b - effBucketCap N)).map (effBucketCap N + ·)

/-- Dense item indices `< n_t` probed for `(b, m)` in `probeDenseListCode`. -/
@[expose]
def bucketProbeDense (N : ℕ) (gm td : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (b m : ℕ) : List ℕ :=
  (bucketProbeSlots N gm L b m).map (fun j => denseOfPhys N gm td (Succinct.slotOf N gm b j))

@[simp]
theorem length_bucketProbeDense (N : ℕ) (gm td : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (b m : ℕ) :
    (bucketProbeDense N gm td L b m).length =
      (L b m).length + (Succinct.bCount N gm b - effBucketCap N) := by
  simp [bucketProbeDense, bucketProbeSlots]

/-- Concrete `BitRAM.Code .standard 12` program for `Dynamic.Op.query u`:
when `N = 0`, sets `r1 = 0` (`none`) in `1` instruction; when `0 < N`, probes
`bucketProbeDense N gm td L b m` via `probeDenseListCode`. -/
@[expose]
noncomputable def queryCode (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (gm td : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (u : Fin U) : BitRAM.Code .standard 12 :=
  if N = 0 then
    .op (.const 1 0)
  else
    let h1 := Succinct.hValOfSeed U N θ
    let b := feistelBucket (bucketBits N) h1 u.val
    let q := keyQuotient (bucketBits N) u.val
    let m := Succinct.mOfSeed U N θ q
    probeDenseListCode U V w N q (bucketProbeDense N gm td L b m)

/-- First matching dense item index for key `u` in `bucketProbeDense` (or `0` if absent). -/
@[expose]
noncomputable def findHitDense (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (gm td : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (s_bit : BitMemory.State) (u : Fin U) : ℕ :=
  let h1 := Succinct.hValOfSeed U N θ
  let b := feistelBucket (bucketBits N) h1 u.val
  let q := keyQuotient (bucketBits N) u.val
  let m := Succinct.mOfSeed U N θ q
  ((bucketProbeDense N gm td L b m).find?
    (fun d => decide (denseQuotAt U V w N s_bit d = q))).getD 0

/-- **Machine-level execution certificate for `queryCode` (`queryCode_exec`):**
for any machine state `x : BitRAM.Data 12` satisfying `Rep U V w N θ s_abs x.toBitMemoryState`,
`queryCode` executes in at most `111 + 37 * probeExcess` `BitRAM` instructions, leaving
`y.toBitMemoryState = x.toBitMemoryState` (thus preserving `Rep` and `bitSize`) and returning
`(if y.regs 1 = 0 then none else some (y.regs 0)) = s_abs u` (and when `(s_abs u).isSome`, placing
its unique dense item index `y.regs 2 = findHitDense ... < (Dynamic.dom s_abs).card` in `r2`). -/
theorem queryCode_exec {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {x : BitRAM.Data 12} {L : ℕ → ℕ → List ℕ}
    (hw : 0 < w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hrep : Rep U V w N θ s_abs x.toBitMemoryState)
    (hL : 0 < N → BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs) x.toBitMemoryState)
    (u : Fin U) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let pe := if N = 0 then 0 else
      probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u
    BitRAM.DemonicExecWithin w (queryCode U V w N θ gm td L u) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        Rep U V w N θ s_abs y.toBitMemoryState ∧
        y.WellFormed w ∧
        (if y.regs 1 = 0 then none else some (y.regs 0)) = s_abs u ∧
        ((s_abs u).isSome →
          y.regs 1 = 1 ∧
          y.regs 2 = findHitDense U V w N θ gm td L x.toBitMemoryState u ∧
          y.regs 2 < (Dynamic.dom s_abs).card ∧
          denseQuotAt U V w N x.toBitMemoryState (y.regs 2) =
            keyQuotient (bucketBits N) u.val ∧
          ∃ j < Succinct.bCount N gm
              (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u.val),
            y.regs 2 = denseOfPhys N gm td
              (Succinct.slotOf N gm
                (feistelBucket (bucketBits N) (Succinct.hValOfSeed U N θ) u.val) j)))
      (111 + 37 * pe) := by
  intro gm td pe
  rcases Nat.eq_zero_or_pos N with rfl | hN_pos
  · have h0 : Fits w 0 := fits_zero w
    have hempty : s_abs = Dynamic.empty U := by
      have hcard0 : (Dynamic.dom s_abs).card = 0 := by
        rcases hrep.epoch_inv with ⟨h0, _⟩ | ⟨_, _, hle, _⟩ <;> omega
      funext k
      by_contra hne
      have hk_in : k ∈ Dynamic.dom s_abs :=
        Dictionary.mem_dom_iff_isSome.mpr (Option.ne_none_iff_isSome.mp hne)
      have : 0 < (Dynamic.dom s_abs).card := Finset.card_pos.mpr ⟨k, hk_in⟩
      omega
    unfold queryCode
    rw [ite_eq_left rfl]
    refine (DemonicExecWithin.const h0 ?_).mono (fun y hy => hy) (by omega)
    have hy_wf : (x.set 1 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi1 : i = 1
      · subst hi1; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi1]
        exact hx.regs_fits i
    refine ⟨rfl, hrep, hy_wf, ?_, ?_⟩
    · rw [hempty]; rfl
    · rw [hempty]; intro h; simp [Dynamic.empty, Dictionary.empty] at h
  · have hN_ne : N ≠ 0 := Nat.ne_of_gt hN_pos
    have hnU : N ≤ U := by
      rcases hrep.epoch_inv with ⟨_, hN0⟩ | ⟨_, _, _, hnU⟩
      · omega
      · exact hnU
    have hn_t : (Dynamic.dom s_abs).card < 2 ^ w :=
      lt_of_le_of_lt (Dynamic.card_dom_le_univ s_abs) hU
    have hinv := hL hN_pos
    have htot := (hrep.active_inv hN_pos).2.1
    set h1 := Succinct.hValOfSeed U N θ
    set b := feistelBucket (bucketBits N) h1 u.val
    set q := keyQuotient (bucketBits N) u.val
    set m := Succinct.mOfSeed U N θ q
    have hb : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
    have hm : m < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
    have hq_fits : Fits w q := by
      have : q ≤ u.val := Nat.div_le_self _ _
      exact Fits.of_le hU (this.trans (le_of_lt u.isLt))
    have hj_mem_slots : ∀ j, j ∈ bucketProbeSlots N gm L b m ↔
        j ∈ L b m ∨ (effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b) := by
      intro j
      unfold bucketProbeSlots
      rw [List.mem_append, List.mem_map]
      refine ⟨?_, ?_⟩
      · rintro (h | ⟨k, hk, rfl⟩)
        · exact Or.inl h
        · rw [List.mem_range] at hk
          exact Or.inr ⟨by omega, by omega⟩
      · rintro (h | ⟨hlo, hhi⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j - effBucketCap N, List.mem_range.mpr (by omega), by omega⟩
    have hj_lt_of_mem : ∀ j ∈ bucketProbeSlots N gm L b m, j < Succinct.bCount N gm b := by
      intro j hj
      rcases (hj_mem_slots j).mp hj with h_in | ⟨_, hhi⟩
      · exact ((hinv.hchain_mem b hb m hm j).mp h_in).1
      · exact hhi
    have hds_lt : ∀ d ∈ bucketProbeDense N gm td L b m, d < (Dynamic.dom s_abs).card := by
      intro d hd
      unfold bucketProbeDense at hd
      rw [List.mem_map] at hd
      obtain ⟨j, hj, rfl⟩ := hd
      rw [← htot]
      exact (denseOfPhys_slotOf_lt_and_injective hinv.hslot hinv.htd).1 b hb j (hj_lt_of_mem j hj)
    have hpe_bound :
        (L b m).length + (Succinct.bCount N gm b - effBucketCap N) ≤
          2 + probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
            (Dynamic.dom s_abs) u :=
      (chain_and_overflow_le_probeExcess_rep θ hinv u).2.2.1
    have hlen_le : 37 + 37 * (bucketProbeDense N gm td L b m).length ≤ 111 + 37 * pe := by
      rw [length_bucketProbeDense]
      dsimp only [pe]
      rw [ite_eq_right hN_ne]
      omega
    unfold queryCode
    rw [ite_eq_right hN_ne]
    refine (probeDenseListCode_exec (bucketProbeDense N gm td L b m)
      hw (le_of_lt hU) hV hn_t hx hds_lt hrep.bitSize_eq.symm.le hq_fits).mono
      (fun y ⟨hst, hy_wf, hres⟩ => ?_) hlen_le
    have hB_eq : Succinct.bucketMapOfState U N h1 s_abs b q = s_abs u :=
      Succinct.bucketMapOfState_feistelBucket hnU h1 s_abs u
    have hex_iff :
        (∃ d ∈ bucketProbeDense N gm td L b m,
          denseQuotAt U V w N x.toBitMemoryState d = q) ↔
        (s_abs u).isSome := by
      rw [← hB_eq, hinv.hmap_dom b hb q]
      constructor
      · rintro ⟨d, hd, hqd⟩
        unfold bucketProbeDense at hd
        rw [List.mem_map] at hd
        obtain ⟨j, hj_in, rfl⟩ := hd
        have hj_lt := hj_lt_of_mem j hj_in
        have hphys_lt : Succinct.slotOf N gm b j < N :=
          (Succinct.slotOf_lt_and_injective hinv.hslot).1 b hb j hj_lt
        refine ⟨j, hj_lt, ?_⟩
        unfold virtualQuotAt
        change (if Succinct.slotOf N gm b j < N then
          denseQuotAt U V w N x.toBitMemoryState (denseOfPhys N gm td (Succinct.slotOf N gm b j))
          else 0) = q
        rw [ite_eq_left hphys_lt]
        exact hqd
      · rintro ⟨j, hj_lt, hvq⟩
        have hvq_virt := hvq
        have hphys_lt : Succinct.slotOf N gm b j < N :=
          (Succinct.slotOf_lt_and_injective hinv.hslot).1 b hb j hj_lt
        unfold virtualQuotAt at hvq
        change (if Succinct.slotOf N gm b j < N then
          denseQuotAt U V w N x.toBitMemoryState (denseOfPhys N gm td (Succinct.slotOf N gm b j))
          else 0) = q at hvq
        rw [ite_eq_left hphys_lt] at hvq
        have hj_in : j ∈ bucketProbeSlots N gm L b m := by
          rw [hj_mem_slots]
          by_cases hj_cap : j < effBucketCap N
          · left
            exact (hinv.hchain_mem b hb m hm j).mpr ⟨hj_lt, hj_cap, by rw [hvq_virt]⟩
          · right
            exact ⟨by omega, hj_lt⟩
        exact ⟨denseOfPhys N gm td (Succinct.slotOf N gm b j),
          List.mem_map.mpr ⟨j, hj_in, rfl⟩, hvq⟩
    refine ⟨hst, hst ▸ hrep, hy_wf, ?_, ?_⟩
    · by_cases his : (s_abs u).isSome
      · rw [ite_eq_left (hex_iff.mpr his)] at hres
        obtain ⟨hr1, _, hd_in, hqd, hr0⟩ := hres
        rw [hr1]
        simp only [Nat.one_ne_zero, ↓reduceIte, hr0]
        unfold bucketProbeDense at hd_in
        rw [List.mem_map] at hd_in
        obtain ⟨j, hj_in, hd_eq⟩ := hd_in
        have hj_lt := hj_lt_of_mem j hj_in
        have hphys_lt : Succinct.slotOf N gm b j < N :=
          (Succinct.slotOf_lt_and_injective hinv.hslot).1 b hb j hj_lt
        have hsome := hinv.hmap_some b hb j hj_lt
        unfold virtualQuotAt virtualValAt at hsome
        change Succinct.bucketMapOfState U N h1 s_abs b
          (if Succinct.slotOf N gm b j < N then
            denseQuotAt U V w N x.toBitMemoryState (denseOfPhys N gm td (Succinct.slotOf N gm b j))
          else 0) =
          some (if Succinct.slotOf N gm b j < N then
            denseValAt U V w N x.toBitMemoryState (denseOfPhys N gm td (Succinct.slotOf N gm b j))
          else 0) at hsome
        rw [ite_eq_left hphys_lt, ite_eq_left hphys_lt, hd_eq, hqd, hB_eq] at hsome
        exact hsome.symm
      · rw [ite_eq_right (mt hex_iff.mp his)] at hres
        simp only [hres, ↓reduceIte]
        exact (Option.not_isSome_iff_eq_none.mp his).symm
    · intro his
      rw [ite_eq_left (hex_iff.mpr his)] at hres
      obtain ⟨hr1, hr2_find, hd_in, hqd, _⟩ := hres
      have hd_lt := hds_lt (y.regs 2) hd_in
      unfold bucketProbeDense at hd_in
      rw [List.mem_map] at hd_in
      obtain ⟨j, hj_in, hd_eq⟩ := hd_in
      exact ⟨hr1, hr2_find, hd_lt, hqd, j, hj_lt_of_mem j hj_in, hd_eq.symm⟩

/-- **Expected `O(1)` instruction bound for `queryCode` (`queryCode_expected_steps`):**
for any active epoch (`0 < N`, `EpochInv U N (Dynamic.dom s_abs).card`) and any key `u : Fin U`,
the expected instruction bound `111 + 37 * probeExcess` of `queryCode` over a uniformly sampled
seed `θ : Succinct.QuotHashSeed U N` is at most `296` `BitRAM` instructions. -/
theorem queryCode_expected_steps {U N : ℕ} {s_abs : Dynamic.State U}
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) (hN : 0 < N) (u : Fin U) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (PMF.uniformOfFintype (Succinct.QuotHashSeed U N)) θ *
        ((111 + 37 *
          probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
            (Dynamic.dom s_abs) u : ℕ) : ℝ≥0∞)) ≤ 296 := by
  rcases hepoch with ⟨_, hN0⟩ | ⟨_, hlo, _, hnU⟩
  · omega
  · have herase : #((Dynamic.dom s_abs).erase u) ≤ N :=
      Finset.card_erase_le.trans hlo
    simpa using Succinct.tsum_affine_probeExcess_reducedPolyHash_le hnU (Dynamic.dom s_abs) u
      herase 111 37
      (fun θ => 111 + 37 *
        probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
          (Dynamic.dom s_abs) u)
      (fun _ => le_rfl)

/-! ## Section 2: Concrete `BitRAM.Code` for in-place `insert` hit (`insertHitCode`) -/

/-- Concrete `BitRAM.Code .standard 12` program for `insert(u, v)` when `u ∈ Dynamic.dom s_abs`:
first probes bucket `b` via `queryCode`, then overwrites the dense item `d_hit` with `(q, v)` via
`writeDenseItemCode` without changing `bitSize` or any metadata word. -/
@[expose]
noncomputable def insertHitCode (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (gm td : ℕ → ℕ) (L : ℕ → ℕ → List ℕ) (s_bit : BitMemory.State)
    (u : Fin U) (v : ℕ) : BitRAM.Code .standard 12 :=
  let q := keyQuotient (bucketBits N) u.val
  let d := findHitDense U V w N θ gm td L s_bit u
  .seq (queryCode U V w N θ gm td L u)
    (writeDenseItemCode U V w N d q v)

private theorem rep_reducedKWise_congr {base w w₀ b b' : ℕ}
    {θ : ReducedPolySeed w₀ b b' 3} {mem₁ mem₂ : ℕ → ℕ}
    (heq : ∀ a < base + ReducedKWise.space w w₀ b b' 3, mem₁ a = mem₂ a)
    (hrep : ReducedKWise.Rep base w w₀ b b' 3 θ mem₂) :
    ReducedKWise.Rep base w w₀ b b' 3 θ mem₁ := by
  rcases hrep with ⟨⟨hword, hentry⟩, ⟨h0, hlimb⟩⟩
  refine ⟨⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩, ⟨?_, fun j m => ?_⟩⟩
  · rw [heq (ReducedKWise.tabBase base w₀ b b' 3 + wIdx)
      (by unfold ReducedKWise.tabBase ReducedKWise.space; omega)]
    exact hword wIdx hwIdx
  · have hsh : idx >>> reducedPackShift (reducedTrinomialStep w₀ b b') w <
        ReducedKWise.tableWords w w₀ b b' :=
      shiftRight_lt_reducedTableWords hidx
    rw [heq (ReducedKWise.tabBase base w₀ b b' 3 +
        idx >>> reducedPackShift (reducedTrinomialStep w₀ b b') w)
      (by unfold ReducedKWise.tabBase ReducedKWise.space; omega)]
    exact hentry idx hidx
  · have hs_pos : 0 < ReducedKWise.seedWords w₀ b b' 3 := ReducedKWise.seedWords_pos w₀ b b' 3
    rw [heq base (by unfold ReducedKWise.space; omega)]
    exact h0
  · have hidx : m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val <
        3 * reducedLimbCount (reducedTrinomialStep w₀ b b') := by
      calc m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val
          < reducedLimbCount (reducedTrinomialStep w₀ b b') +
              reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val :=
            Nat.add_lt_add_right m.isLt _
        _ = (j.val + 1) * reducedLimbCount (reducedTrinomialStep w₀ b b') := by ring
        _ ≤ 3 * reducedLimbCount (reducedTrinomialStep w₀ b b') :=
            Nat.mul_le_mul_right _ j.isLt
    rw [heq (base + 1 + (m.val + reducedLimbCount (reducedTrinomialStep w₀ b b') * j.val))
      (by unfold ReducedKWise.space ReducedKWise.seedWords; omega)]
    exact hlimb j m

/-- Whenever `mem₁` and `mem₂` agree on all metadata words `< epochMetaWords U w N` (`0 < w`,
`0 < N`), they induce identical `gmAtBit`, `lmAtBit`, `tdAtBit`, `dtAtBit`, and
`ReducedKWise.Rep`. -/
theorem meta_congr_of_mem_eq_lt_epochMetaWords {U w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {mem₁ mem₂ : ℕ → ℕ} (hw : 0 < w) (hN : 0 < N)
    (heq : ∀ a < epochMetaWords U w N, mem₁ a = mem₂ a) :
    gmAtBit U w N mem₁ = gmAtBit U w N mem₂ ∧
    lmAtBit U w N mem₁ = lmAtBit U w N mem₂ ∧
    tdAtBit U w N mem₁ = tdAtBit U w N mem₂ ∧
    dtAtBit U w N mem₁ = dtAtBit U w N mem₂ ∧
    (ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ mem₂ →
     ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ mem₁) := by
  have hN_ne : N ≠ 0 := Nat.ne_of_gt hN
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · funext idx
    unfold gmAtBit
    split_ifs with hidx
    · have hlt := wordOffset_add_one_lt_packedWords (k := globalPtrBits N) hw hidx
      have hmeta : offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w ≤
          epochMetaWords U w N := by
        unfold epochMetaWords offGM offLM offHash
        rw [ite_eq_right hN_ne]
        omega
      unfold readPacked
      dsimp only
      rw [heq _ (by omega), heq _ (by omega)]
    · rfl
  · funext ⟨c, idx⟩
    unfold lmAtBit
    dsimp only
    split_ifs with hp
    · have hlt := wordOffset_add_one_lt_packedWords (k := effBucketPosBits N) hw hp.2
      have hsub : (c + 1) * packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
          9 * packedWords (totalMicroBuckets N) (effBucketPosBits N) w :=
        Nat.mul_le_mul_right _ hp.1
      rw [Nat.add_one_mul] at hsub
      have hmeta : offLM U w N + 9 * packedWords (totalMicroBuckets N) (effBucketPosBits N) w ≤
          epochMetaWords U w N := by
        unfold epochMetaWords offLM offHash Succinct.lmSubWords
        rw [ite_eq_right hN_ne]
        omega
      unfold readPacked
      dsimp only
      rw [heq _ (by unfold offLMSub Succinct.lmSubWords; omega),
        heq _ (by unfold offLMSub Succinct.lmSubWords; omega)]
    · rfl
  · funext idx
    unfold tdAtBit
    split_ifs with hidx
    · have hlt := wordOffset_add_one_lt_packedWords (k := globalPtrBits N) hw hidx
      have hmeta : offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w ≤
          epochMetaWords U w N := by
        unfold epochMetaWords offTD offGM offLM offHash
        rw [ite_eq_right hN_ne]
        omega
      unfold readPacked
      dsimp only
      rw [heq _ (by omega), heq _ (by omega)]
    · rfl
  · funext idx
    unfold dtAtBit
    split_ifs with hidx
    · have hlt := wordOffset_add_one_lt_packedWords (k := globalPtrBits N) hw hidx
      have hmeta := offDT_add_eq_epochMetaWords (U := U) (w := w) hN
      unfold readPacked
      dsimp only
      rw [heq _ (by omega), heq _ (by omega)]
    · rfl
  · intro hrep
    have hhash_le : offHash + Succinct.hashSpace U w N ≤ epochMetaWords U w N := by
      unfold epochMetaWords offHash
      rw [ite_eq_right hN_ne]
      omega
    unfold Succinct.hashSpace at hhash_le
    exact rep_reducedKWise_congr (fun a ha => heq a (lt_of_lt_of_le ha hhash_le)) hrep

/-- **Machine-level execution certificate for `insertHitCode` (`insertHitCode_exec`):**
when `(s_abs u).isSome` and `v < V`, `insertHitCode` executes in at most `201 + 37 * pe` `BitRAM`
instructions, preserving `bitSize` and all metadata words `< epochMetaWords U w N`, and
establishing `Rep U V w N θ (Function.update s_abs u (some v)) y.toBitMemoryState`. -/
theorem insertHitCode_exec {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {x : BitRAM.Data 12} {L : ℕ → ℕ → List ℕ}
    (hw : 0 < w) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hrep : Rep U V w N θ s_abs x.toBitMemoryState)
    (hL : 0 < N → BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs) x.toBitMemoryState)
    (u : Fin U) {v : ℕ} (hv : v < V) (his : (s_abs u).isSome) :
    let gm := gmAtBit U w N x.mem
    let td := tdAtBit U w N x.mem
    let pe := if N = 0 then 0 else
      probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
        (Dynamic.dom s_abs) u
    BitRAM.DemonicExecWithin w
      (insertHitCode U V w N θ gm td L x.toBitMemoryState u v) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = x.bitSize ∧
        Rep U V w N θ (Function.update s_abs u (some v)) y.toBitMemoryState ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        gmAtBit U w N y.mem = gm)
      (201 + 37 * pe) := by
  intro gm td pe
  have hdom_u : u ∈ Dynamic.dom s_abs := Dictionary.mem_dom_iff_isSome.mpr his
  have hcard_pos : 0 < (Dynamic.dom s_abs).card := Finset.card_pos.mpr ⟨u, hdom_u⟩
  have hN_pos : 0 < N := by
    rcases hrep.epoch_inv with ⟨h0, _⟩ | ⟨hN, _, _, _⟩ <;> omega
  have hnU : N ≤ U := by
    rcases hrep.epoch_inv with ⟨_, hN0⟩ | ⟨_, _, _, hnU⟩
    · omega
    · exact hnU
  have hinv := hL hN_pos
  have htot := (hrep.active_inv hN_pos).2.1
  set h1 := Succinct.hValOfSeed U N θ
  set b := feistelBucket (bucketBits N) h1 u.val
  set q := keyQuotient (bucketBits N) u.val
  set d := findHitDense U V w N θ gm td L x.toBitMemoryState u
  have hb : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
  have hq_fits : Fits (quotientBits U N) q :=
    keyQuotient_lt_two_pow_quotientBits hnU u.isLt
  have hv_fits : Fits (valBits V) v :=
    lt_of_lt_of_le hv (Nat.le_pow_clog (by decide) V)
  refine .seq (T₁ := 111 + 37 * pe) (T₂ := 90)
    (queryCode_exec hw hU hV hx hrep hL u)
    (fun y₁ ⟨hst₁, _, hy₁_wf, _, hhit⟩ => ?_) (by omega)
  obtain ⟨_, hr2_d, hr2_lt, hqd_eq, j, hj_lt, hr2_slot⟩ := hhit his
  have hd_lt : d < (Dynamic.dom s_abs).card := by
    have h := hr2_lt; rwa [hr2_d] at h
  have hqd : denseQuotAt U V w N x.toBitMemoryState d = q := by
    have h := hqd_eq; rwa [hr2_d] at h
  have hd_slot : d = denseOfPhys N gm td (Succinct.slotOf N gm b j) := by
    have h := hr2_slot; rwa [hr2_d] at h
  have hy₁_sz : dictBitSize U V w N (Dynamic.dom s_abs).card ≤ y₁.bitSize := by
    change _ ≤ y₁.toBitMemoryState.bitSize
    rw [hst₁, hrep.bitSize_eq]
  refine (writeDenseItemCode_exec hw (le_of_lt hU) hV hy₁_wf hd_lt hy₁_sz hq_fits hv_fits).mono
    (fun y ⟨hy_wf, hy_sz₁, hy_q_d, hy_v_d, hy_other, hy_meta⟩ => ?_) le_rfl
  have hy_sz : y.bitSize = x.bitSize :=
    hy_sz₁.trans (congrArg BitMemory.State.bitSize hst₁)
  have hy_meta_x : ∀ a < epochMetaWords U w N, y.mem a = x.mem a := by
    intro a ha
    exact (hy_meta a ha).trans (congrFun (congrArg BitMemory.State.mem hst₁) a)
  obtain ⟨hgm_eq, hlm_eq, htd_eq, hdt_eq, hhash_congr⟩ :=
    meta_congr_of_mem_eq_lt_epochMetaWords (θ := θ) hw hN_pos hy_meta_x
  have hq_all : ∀ d' < (Dynamic.dom s_abs).card,
      denseQuotAt U V w N y.toBitMemoryState d' =
        denseQuotAt U V w N x.toBitMemoryState d' := by
    intro d' hd'
    by_cases heq : d' = d
    · subst heq; exact hy_q_d.trans hqd.symm
    · have h1 := (hy_other d' hd' heq).1
      rw [hst₁] at h1
      exact h1
  have hvq_all : ∀ b' < numBuckets N, ∀ j' < Succinct.bCount N gm b',
      virtualQuotAt U V w N y.toBitMemoryState (Succinct.slotOf N gm b' j') =
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b' j') := by
    intro b' hb' j' hj'
    have hphys_lt : Succinct.slotOf N gm b' j' < N :=
      (Succinct.slotOf_lt_and_injective hinv.hslot).1 b' hb' j' hj'
    have hd'_lt : denseOfPhys N gm td (Succinct.slotOf N gm b' j') < (Dynamic.dom s_abs).card := by
      rw [← htot]
      exact (denseOfPhys_slotOf_lt_and_injective hinv.hslot hinv.htd).1 b' hb' j' hj'
    unfold virtualQuotAt
    change (if Succinct.slotOf N gm b' j' < N then
        denseQuotAt U V w N y.toBitMemoryState
          (denseOfPhys N (gmAtBit U w N y.mem) (tdAtBit U w N y.mem) (Succinct.slotOf N gm b' j'))
      else 0) =
      (if Succinct.slotOf N gm b' j' < N then
        denseQuotAt U V w N x.toBitMemoryState
          (denseOfPhys N gm td (Succinct.slotOf N gm b' j'))
      else 0)
    rw [ite_eq_left hphys_lt, ite_eq_left hphys_lt, hgm_eq, htd_eq]
    exact hq_all _ hd'_lt
  have hdom_upd : Dynamic.dom (Function.update s_abs u (some v)) = Dynamic.dom s_abs := by
    ext k
    simp only [Dictionary.mem_dom_iff_isSome]
    by_cases hku : k = u
    · subst hku; rw [Function.update_self, Option.isSome_some, his]
    · rw [Function.update_of_ne hku]
  have hcard_upd : (Dynamic.dom (Function.update s_abs u (some v))).card =
      (Dynamic.dom s_abs).card :=
    congrArg Finset.card hdom_upd
  have hinv_y : BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N h1 (Function.update s_abs u (some v)))
      y.toBitMemoryState := by
    refine
      { hslot := by
          change Succinct.SlotStoreInv N (gmAtBit U w N y.mem)
          rw [hgm_eq]; exact hinv.hslot
        htd := by
          change TailDenseInv N (gmAtBit U w N y.mem 0) (gmAtBit U w N y.mem 1)
            (tdAtBit U w N y.mem) (dtAtBit U w N y.mem)
          rw [hgm_eq, htd_eq, hdt_eq]; exact hinv.htd
        hchains := by
          change Succinct.AllChainsValid N (lmAtBit U w N y.mem) L
          rw [hlm_eq]; exact hinv.hchains
        hchain_mem := fun b' hb' m' hm' j' => by
          change j' ∈ L b' m' ↔
            j' < Succinct.bCount N (gmAtBit U w N y.mem) b' ∧
            j' < effBucketCap N ∧
            Succinct.mOfSeed U N θ
              (virtualQuotAt U V w N y.toBitMemoryState
                (Succinct.slotOf N (gmAtBit U w N y.mem) b' j')) = m'
          rw [hgm_eq, hinv.hchain_mem b' hb' m' hm' j']
          constructor
          · rintro ⟨hj', hcap, hm_eq⟩
            refine ⟨hj', hcap, ?_⟩
            have hvq := hvq_all b' hb' j' hj'
            dsimp only [gm] at hvq
            rw [hvq]
            exact hm_eq
          · rintro ⟨hj', hcap, hm_eq⟩
            refine ⟨hj', hcap, ?_⟩
            have hvq := hvq_all b' hb' j' hj'
            dsimp only [gm] at hvq
            rw [hvq] at hm_eq
            exact hm_eq
        hnodup_q := fun b' hb' j₁ hj₁ j₂ hj₂ heq => by
          change j₁ < Succinct.bCount N (gmAtBit U w N y.mem) b' at hj₁
          change j₂ < Succinct.bCount N (gmAtBit U w N y.mem) b' at hj₂
          change virtualQuotAt U V w N y.toBitMemoryState
              (Succinct.slotOf N (gmAtBit U w N y.mem) b' j₁) =
            virtualQuotAt U V w N y.toBitMemoryState
              (Succinct.slotOf N (gmAtBit U w N y.mem) b' j₂) at heq
          rw [hgm_eq] at hj₁ hj₂ heq
          rw [hvq_all b' hb' j₁ hj₁, hvq_all b' hb' j₂ hj₂] at heq
          exact hinv.hnodup_q b' hb' j₁ hj₁ j₂ hj₂ heq
        hmap_some := ?_
        hmap_dom := ?_ }
    · intro b' hb' j' hj'
      change j' < Succinct.bCount N (gmAtBit U w N y.mem) b' at hj'
      change Succinct.bucketMapOfState U N h1 (Function.update s_abs u (some v)) b'
          (virtualQuotAt U V w N y.toBitMemoryState
            (Succinct.slotOf N (gmAtBit U w N y.mem) b' j')) =
        some (virtualValAt U V w N y.toBitMemoryState
          (Succinct.slotOf N (gmAtBit U w N y.mem) b' j'))
      rw [hgm_eq] at hj' ⊢
      have hphys_lt : Succinct.slotOf N gm b' j' < N :=
        (Succinct.slotOf_lt_and_injective hinv.hslot).1 b' hb' j' hj'
      rw [hvq_all b' hb' j' hj']
      by_cases hbj : b' = b ∧ j' = j
      · rcases hbj with ⟨rfl, hj_eq⟩
        subst hj_eq
        have hvq_bj : virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j') = q := by
          unfold virtualQuotAt
          change (if Succinct.slotOf N gm b j' < N then
            denseQuotAt U V w N x.toBitMemoryState
              (denseOfPhys N gm td (Succinct.slotOf N gm b j'))
            else 0) = q
          rw [ite_eq_left hphys_lt, ← hd_slot, hqd]
        have hvv_bj : virtualValAt U V w N y.toBitMemoryState (Succinct.slotOf N gm b j') = v := by
          unfold virtualValAt
          change (if Succinct.slotOf N gm b j' < N then
            denseValAt U V w N y.toBitMemoryState
              (denseOfPhys N (gmAtBit U w N y.mem) (tdAtBit U w N y.mem)
                (Succinct.slotOf N gm b j'))
            else 0) = v
          rw [ite_eq_left hphys_lt, hgm_eq, htd_eq, ← hd_slot, hy_v_d]
        rw [hvq_bj, hvv_bj]
        have hB_upd :
            Succinct.bucketMapOfState U N h1 (Function.update s_abs u (some v)) b q =
              (Function.update s_abs u (some v)) u :=
          Succinct.bucketMapOfState_feistelBucket hnU h1 (Function.update s_abs u (some v)) u
        rw [hB_upd, Function.update_self]
      · have hd'_ne : denseOfPhys N gm td (Succinct.slotOf N gm b' j') ≠ d := by
          intro heq
          rw [hd_slot] at heq
          have hinj := (denseOfPhys_slotOf_lt_and_injective hinv.hslot hinv.htd).2
            b' hb' j' hj' b hb j hj_lt heq
          exact hbj hinj
        have hd'_lt : denseOfPhys N gm td (Succinct.slotOf N gm b' j') <
            (Dynamic.dom s_abs).card := by
          rw [← htot]
          exact (denseOfPhys_slotOf_lt_and_injective hinv.hslot hinv.htd).1 b' hb' j' hj'
        have hvv_eq :
            virtualValAt U V w N y.toBitMemoryState (Succinct.slotOf N gm b' j') =
              virtualValAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b' j') := by
          unfold virtualValAt
          change (if Succinct.slotOf N gm b' j' < N then
              denseValAt U V w N y.toBitMemoryState
                (denseOfPhys N (gmAtBit U w N y.mem) (tdAtBit U w N y.mem)
                  (Succinct.slotOf N gm b' j'))
            else 0) =
            (if Succinct.slotOf N gm b' j' < N then
              denseValAt U V w N x.toBitMemoryState
                (denseOfPhys N gm td (Succinct.slotOf N gm b' j'))
            else 0)
          rw [ite_eq_left hphys_lt, ite_eq_left hphys_lt, hgm_eq, htd_eq]
          have h2 := (hy_other _ hd'_lt hd'_ne).2
          rw [hst₁] at h2
          exact h2
        have hsome_x :
            Succinct.bucketMapOfState U N h1 s_abs b'
              (virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b' j')) =
            some (virtualValAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b' j')) :=
          hinv.hmap_some b' hb' j' hj'
        rw [hvv_eq, ← hsome_x, ← Succinct.bucketMapOfState_update hnU h1]
        set q' := virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b' j')
        by_cases hbeq : b' = b
        · subst hbeq
          rw [Function.update_self]
          have hj'_ne : j' ≠ j := fun h => hbj ⟨rfl, h⟩
          have hvq_j : virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q := by
            unfold virtualQuotAt
            change (if Succinct.slotOf N gm b j < N then
              denseQuotAt U V w N x.toBitMemoryState
                (denseOfPhys N gm td (Succinct.slotOf N gm b j))
              else 0) = q
            have hlt_j : Succinct.slotOf N gm b j < N :=
              (Succinct.slotOf_lt_and_injective hinv.hslot).1 b hb j hj_lt
            rw [ite_eq_left hlt_j, ← hd_slot, hqd]
          have hq'_ne : q' ≠ q := by
            intro hq_eq
            exact hj'_ne (hinv.hnodup_q b hb j' hj' j hj_lt (hq_eq.trans hvq_j.symm))
          rw [Function.update_of_ne hq'_ne]
        · rw [Function.update_of_ne hbeq]
    · intro b' hb' q'
      change (Succinct.bucketMapOfState U N h1 (Function.update s_abs u (some v)) b' q').isSome ↔
        ∃ j' < Succinct.bCount N (gmAtBit U w N y.mem) b',
          virtualQuotAt U V w N y.toBitMemoryState
            (Succinct.slotOf N (gmAtBit U w N y.mem) b' j') = q'
      rw [hgm_eq]
      have hdom_eq :
          (Succinct.bucketMapOfState U N h1 (Function.update s_abs u (some v)) b' q').isSome =
            (Succinct.bucketMapOfState U N h1 s_abs b' q').isSome := by
        unfold Succinct.bucketMapOfState
        split_ifs with hrec
        · by_cases heq_u : (⟨feistelReconstruct (bucketBits N) h1 b' q', hrec.1⟩ : Fin U) = u
          · rw [heq_u, Function.update_self, Option.isSome_some, his]
          · rw [Function.update_of_ne heq_u]
        · rfl
      rw [hdom_eq, hinv.hmap_dom b' hb' q']
      constructor
      · rintro ⟨j', hj', hvq'⟩
        exact ⟨j', hj', (hvq_all b' hb' j' hj').trans hvq'⟩
      · rintro ⟨j', hj', hvq'⟩
        exact ⟨j', hj', (hvq_all b' hb' j' hj').symm.trans hvq'⟩
  have hrep_y : Rep U V w N θ (Function.update s_abs u (some v)) y.toBitMemoryState := by
    have hact := hrep.active_inv hN_pos
    have h4 : 4 ≤ epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
    have hhdr0 : x.mem 0 = (Dynamic.dom s_abs).card := hrep.hdr_count
    have hhdr1 : x.mem 1 = N := hrep.hdr_cap
    have hhdr2 : x.mem 2 = itemBits U V N := hrep.hdr_itemBits
    have hhdr3 : x.mem 3 = epochMetaBits U w N := hrep.hdr_metaBits
    refine
      { wellFormed := hy_wf.mem_wf
        bitSize_eq := by
          change y.bitSize = _
          rw [hy_sz, hcard_upd]
          exact hrep.bitSize_eq
        epoch_inv := by rw [hcard_upd]; exact hrep.epoch_inv
        values_bounded := by
          intro k w_val hkw
          by_cases hku : k = u
          · subst hku
            rw [Function.update_self] at hkw
            injection hkw with hvw
            subst hvw
            exact hv
          · rw [Function.update_of_ne hku] at hkw
            exact hrep.values_bounded k w_val hkw
        hdr_count := by
          change y.mem 0 = (Dynamic.dom (Function.update s_abs u (some v))).card
          rw [hy_meta_x 0 (by omega), hhdr0, hcard_upd]
        hdr_cap := by
          change y.mem 1 = N
          rw [hy_meta_x 1 (by omega), hhdr1]
        hdr_itemBits := by
          change y.mem 2 = itemBits U V N
          rw [hy_meta_x 2 (by omega), hhdr2]
        hdr_metaBits := by
          change y.mem 3 = epochMetaBits U w N
          rw [hy_meta_x 3 (by omega), hhdr3]
        active_inv := fun _ => by
          refine ⟨hhash_congr hact.1, ?_, ⟨L, hinv_y⟩⟩
          change Succinct.totalSlots N (gmAtBit U w N y.mem) =
            (Dynamic.dom (Function.update s_abs u (some v))).card
          rw [hgm_eq, hcard_upd]
          exact hact.2.1 }
  exact ⟨hy_wf, hy_sz, hrep_y, hy_meta_x, hgm_eq⟩

/-- **Expected `O(1)` instruction bound for `insertHitCode` (`insertHitCode_expected_steps`):**
for any active epoch (`0 < N`, `EpochInv U N (Dynamic.dom s_abs).card`) and any key `u : Fin U`,
the expected instruction bound `201 + 37 * probeExcess` of `insertHitCode` over a uniformly sampled
seed `θ : Succinct.QuotHashSeed U N` is at most `386` `BitRAM` instructions. -/
theorem insertHitCode_expected_steps {U N : ℕ} {s_abs : Dynamic.State U}
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) (hN : 0 < N) (u : Fin U) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (PMF.uniformOfFintype (Succinct.QuotHashSeed U N)) θ *
        ((201 + 37 *
          probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
            (Dynamic.dom s_abs) u : ℕ) : ℝ≥0∞)) ≤ 386 := by
  rcases hepoch with ⟨_, hN0⟩ | ⟨_, hlo, _, hnU⟩
  · omega
  · have herase : #((Dynamic.dom s_abs).erase u) ≤ N :=
      Finset.card_erase_le.trans hlo
    simpa using Succinct.tsum_affine_probeExcess_reducedPolyHash_le hnU (Dynamic.dom s_abs) u
      herase 201 37
      (fun θ => 201 + 37 *
        probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2
          (Dynamic.dom s_abs) u)
      (fun _ => le_rfl)

end Cslib.DataStructure.Dictionary.BitResizable
