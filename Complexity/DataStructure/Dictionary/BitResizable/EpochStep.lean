/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.DeleteStep
import all Complexity.DataStructure.Dictionary.WordRAM.SuccinctHash

/-!
# Uniform Compiled In-Epoch Operations and Epoch Representation Invariants

This module wires the uniform parameter-free `BitRAM.Code .standard 280` in-epoch dictionary
programs (`queryRegCode`, `inEpochInsertRegCode`, `inEpochDeleteRegCode`) together with header
synchronization (`syncHdrCountRegCode`), empty-dictionary initialization (`initEmptyRegCode`),
and unified operation dispatch (`inEpochStepRegCode`), establishing end-to-end execution
certificates under demonic `.grow` (`BitRAM.DemonicExecWithin`) and deterministic fuel evaluation
(`BitRAM.evalWithOracle`).

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.EpochDictInv`: full register-and-memory epoch
  dictionary invariant coupling `BitRAM.Data 280` with `s_abs : Dynamic.State U` and
  `s_fix : Memory.State`.
* `Cslib.DataStructure.Dictionary.BitResizable.decodeQueryRegs`,
  `Cslib.DataStructure.Dictionary.BitResizable.OpOutputCorrect`,
  `Cslib.DataStructure.Dictionary.BitResizable.loadOpRegs`: calling convention and output
  specification on `BitRAM.Data 280`.
* `Cslib.DataStructure.Dictionary.BitResizable.initEmptyRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.syncHdrCountRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.queryOpRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.inEpochInsertOpRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.inEpochDeleteOpRegCode`,
  `Cslib.DataStructure.Dictionary.BitResizable.inEpochStepRegCode`: fixed uniform parameter-free
  `BitRAM.Code .standard 280` programs.

## Main results

* `Cslib.DataStructure.Dictionary.BitResizable.EpochDictInv.rep`: every `EpochDictInv` state in the
  active-epoch hysteresis window `EpochInv` satisfies the single-tape bit-resizable dictionary
  invariant `Rep` and tight bit-space bound.
* `Cslib.DataStructure.Dictionary.BitResizable.initEmptyRegCode_exec`: initializes the empty
  dictionary from `bitSize = 0` in `8 * w + 37` instructions under demonic `.grow`.
* `Cslib.DataStructure.Dictionary.BitResizable.inEpochStepRegCode_exec`: executes any valid
  in-epoch `query`, `insert`, or `delete` via the fixed program `inEpochStepRegCode` in
  `O(1)` expected amortized instructions against `1967 * inEpochPotential`.
* `Cslib.DataStructure.Dictionary.BitResizable.exists_empty_epochDictInv`: non-vacuity and
  active-epoch initialization witness constructing an `EpochDictInv` state for `Dynamic.empty U`
  at any epoch capacity `N ≤ U` and seed `θ` with `inEpochPotential = 0`.
-/

public section

namespace Cslib.DataStructure.Dictionary.BitResizable

open Cslib.WordRAM Cslib.WordRAM.BitRAM
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Memory.BitPacking Cslib.DataStructure.Memory.BitMemory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.Probability
open Finset
open scoped ENNReal BigOperators

/-! ## Section 1: Calling convention, potential, and `EpochDictInv` -/

/-- Probe excess for key `u` in state `s_abs` under epoch capacity `N` and seed `θ`. -/
noncomputable abbrev epochProbeExcess (U N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (u : Fin U) : ℕ :=
  probeExcess N (Succinct.qStage1 U N θ.1) (Succinct.polyStage2 U N) θ.2 (Dynamic.dom s_abs) u

/-- Slab-rebalancing potential `Succinct.slotPotential` of a fixed-capacity companion state `s_fix`
at epoch capacity `N`. -/
@[expose]
def inEpochPotential (U V w N : ℕ) (s_fix : Memory.State) : ℕ :=
  if N = 0 then 0
  else Succinct.slotPotential N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem)

/-- Target key `u : Fin U` of a dynamic dictionary operation `op : Dynamic.Op U`. -/
@[expose]
def opKey {U : ℕ} : Dynamic.Op U → Fin U
  | .query u => u
  | .insert u _ => u
  | .delete u => u

/-- Decode a dictionary `query` result from registers `(r0, r1)`: `none` when `r0 = 0`, and
`some r1` when `r0 ≠ 0`. -/
@[expose]
def decodeQueryRegs (regs : Fin 280 → ℕ) : Option ℕ :=
  if regs 0 = 0 then none else some (regs 1)

/-- Post-operation register output correctness for `op : Dynamic.Op U` against pre-state `s_abs`. -/
@[expose]
def OpOutputCorrect {U : ℕ} (s_abs : Dynamic.State U) (op : Dynamic.Op U)
    (regs : Fin 280 → ℕ) : Prop :=
  match op with
  | .query u => decodeQueryRegs regs = s_abs u
  | .insert _ _ => True
  | .delete _ => True

/-- Load the encoded arguments of `op : Dynamic.Op U` into argument registers
`(r278 = tag, r270 = key, r274 = val)`, preserving memory, `bitSize`, and `EpochRegs`
(`240..269`). -/
@[expose]
def loadOpRegs {U : ℕ} (op : Dynamic.Op U) (x : BitRAM.Data 280) : BitRAM.Data 280 :=
  match op with
  | .query u => ((x.set 278 0).set 270 u.val).set 274 0
  | .insert u v => ((x.set 278 1).set 270 u.val).set 274 v
  | .delete u => ((x.set 278 2).set 270 u.val).set 274 0

theorem EpochInv.card_le {U N m : ℕ} (h : EpochInv U N m) : m ≤ N := by
  rcases h with ⟨h0, rfl⟩ | ⟨_, hle, _, _⟩ <;> omega

theorem EpochInv.cap_le_univ {U N m : ℕ} (h : EpochInv U N m) : N ≤ U := by
  rcases h with ⟨_, rfl⟩ | ⟨_, _, _, hNU⟩
  · exact Nat.zero_le U
  · exact hNU

theorem EpochInv.pos_of_card_pos {U N m : ℕ} (h : EpochInv U N m) (hm : 0 < m) : 0 < N := by
  rcases h with ⟨h0, _⟩ | ⟨hpos, _, _, _⟩ <;> omega

/-- Full register-and-memory epoch dictionary invariant on `BitRAM.Data 280` coupling an abstract
dictionary state `s_abs : Dynamic.State U` and fixed-capacity companion state `s_fix : Memory.State`
at epoch capacity `N ≤ U` and hash seed `θ`. -/
structure EpochDictInv (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (s_fix : Memory.State) (x : BitRAM.Data 280) : Prop where
  wf : x.WellFormed w
  epoch_regs : EpochRegs U V w N x
  cap_le : N ≤ U
  card_le : (Dynamic.dom s_abs).card ≤ N
  val_bounded : Dynamic.ValuesBounded V s_abs
  fit_cap : Fits w (dictBitSize U V w N N)
  bitSize_eq : x.bitSize = dictBitSize U V w N (Dynamic.dom s_abs).card
  hdr_count : x.mem 0 = (Dynamic.dom s_abs).card
  hdr_cap : x.mem 1 = N
  hdr_itemBits : x.mem 2 = itemBits U V N
  hdr_metaBits : x.mem 3 = epochMetaBits U w N
  active : 0 < N →
    Succinct.DictStateInv U V w N 0 θ s_abs s_fix ∧
    FixedCoupled U V w N s_fix x.toBitMemoryState ∧
    ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ x.mem

/-- Every `EpochDictInv` state satisfying the hysteresis condition `EpochInv U N n_t` satisfies the
single-tape bit-resizable `Rep` invariant. -/
theorem EpochDictInv.rep {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (h : EpochDictInv U V w N θ s_abs s_fix x)
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) :
    Rep U V w N θ s_abs x.toBitMemoryState where
  wellFormed := h.wf.mem_wf
  bitSize_eq := h.bitSize_eq
  epoch_inv := hepoch
  values_bounded := h.val_bounded
  hdr_count := h.hdr_count
  hdr_cap := h.hdr_cap
  hdr_itemBits := h.hdr_itemBits
  hdr_metaBits := h.hdr_metaBits
  active_inv hN := by
    obtain ⟨hdict, hcpl, hhash⟩ := h.active hN
    obtain ⟨L, hb_inv⟩ := hdict.hbucket
    have hgm : gmAtBit U w N x.mem = _ := hcpl.gm_eq
    refine ⟨hhash, ?_, L, bucketRepInv_of_fixedCoupled hb_inv hcpl⟩
    change Succinct.totalSlots N (gmAtBit U w N x.mem) = (Dynamic.dom s_abs).card
    rw [hgm, hdict.htot]

/-- Pointwise succinct bit-space bound for any `EpochDictInv` state in the hysteresis window
`EpochInv U N n_t` (`0 < w`, `U ≤ 2 ^ w`). -/
theorem EpochDictInv.space_tight {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (h : EpochDictInv U V w N θ s_abs s_fix x)
    (hepoch : EpochInv U N (Dynamic.dom s_abs).card) :
    let n_t := (Dynamic.dom s_abs).card
    x.bitSize ≤
      Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w :=
  rep_bitSize_le_optBits hw hU (h.rep hepoch)

theorem loadOpRegs_preserves_inv {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (h : EpochDictInv U V w N θ s_abs s_fix x)
    {op : Dynamic.Op U} (hvalid : (Dynamic.spec U V N).valid s_abs op) :
    EpochDictInv U V w N θ s_abs s_fix (loadOpRegs op x) := by
  have h0 : Fits w 0 := fits_zero w
  have h1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  have h2 : Fits w 2 := by
    have h4_meta : 4 ≤ epochMetaWords U w N := by
      unfold epochMetaWords; split_ifs <;> omega
    have h4w : 4 * w < 2 ^ w :=
      h.fit_cap.of_le ((Nat.mul_le_mul_right w h4_meta).trans (Nat.le_add_right _ _))
    exact Fits.of_le h4w (by omega)
  cases op with
  | query u =>
    have hu : Fits w u.val := hU.of_le u.isLt.le
    exact ⟨wf_set 274 (wf_set 270 (wf_set 278 h.wf h0) hu) h0,
      ((h.epoch_regs.set_of_outside (Or.inr (by decide)) 0).set_of_outside
        (Or.inr (by decide)) u.val).set_of_outside (Or.inr (by decide)) 0,
      h.cap_le, h.card_le, h.val_bounded, h.fit_cap, h.bitSize_eq, h.hdr_count, h.hdr_cap,
      h.hdr_itemBits, h.hdr_metaBits, h.active⟩
  | insert u v =>
    have hu : Fits w u.val := hU.of_le u.isLt.le
    have hv : Fits w v := hV.of_le hvalid.2.le
    exact ⟨wf_set 274 (wf_set 270 (wf_set 278 h.wf h1) hu) hv,
      ((h.epoch_regs.set_of_outside (Or.inr (by decide)) 1).set_of_outside
        (Or.inr (by decide)) u.val).set_of_outside (Or.inr (by decide)) v,
      h.cap_le, h.card_le, h.val_bounded, h.fit_cap, h.bitSize_eq, h.hdr_count, h.hdr_cap,
      h.hdr_itemBits, h.hdr_metaBits, h.active⟩
  | delete u =>
    have hu : Fits w u.val := hU.of_le u.isLt.le
    exact ⟨wf_set 274 (wf_set 270 (wf_set 278 h.wf h2) hu) h0,
      ((h.epoch_regs.set_of_outside (Or.inr (by decide)) 2).set_of_outside
        (Or.inr (by decide)) u.val).set_of_outside (Or.inr (by decide)) 0,
      h.cap_le, h.card_le, h.val_bounded, h.fit_cap, h.bitSize_eq, h.hdr_count, h.hdr_cap,
      h.hdr_itemBits, h.hdr_metaBits, h.active⟩

/-! ## Section 2: Frame helpers and uniform header-count synchronization (`syncHdrCountRegCode`) -/

/-- Writing a `w`-bit word at address `a` strictly inside the allocated complete words
(`(a + 1) * w ≤ x.bitSize`) preserves `Data.WellFormed w`. -/
theorem wf_write_of_word_lt {w r a v : ℕ} (hw : 0 < w) {x : BitRAM.Data r}
    (hx : x.WellFormed w) (hv : Fits w v) (ha : (a + 1) * w ≤ x.bitSize) :
    (x.write a v).WellFormed w where
  regs_fits := hx.regs_fits
  mem_wf := {
    mem_fits q := by
      change Fits w (Function.update x.mem a v q)
      by_cases hq : q = a
      · subst hq; rw [Function.update_self]; exact hv
      · rw [Function.update_of_ne hq]; exact hx.mem_wf.mem_fits q
    bitSize_fits := hx.mem_wf.bitSize_fits
    zero_above i hi := by
      have hge : a + 1 ≤ i / w := (Nat.le_div_iff_mul_le hw).mpr (ha.trans hi)
      have hne : 0 + i / w ≠ a := by omega
      change (Function.update x.mem a v (0 + i / w)).testBit (i % w) = false
      rw [Function.update_of_ne hne]
      exact hx.mem_wf.zero_above i hi
  }

/-- `ReducedKWise.Rep` at `offHash` depends only on words in `[offHash, offLM U w N)`. -/
theorem reducedKWise_rep_congr {U w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {m₁ m₂ : ℕ → ℕ}
    (hrep : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ m₁)
    (heq : ∀ a, offHash ≤ a → a < offLM U w N → m₂ a = m₁ a) :
    ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ m₂ := by
  rcases hrep with ⟨⟨htab1, htab2⟩, hseed0, hseed_limbs⟩
  refine ⟨⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩, ?_, fun j m => ?_⟩
  · have ha_lo : offHash ≤ ReducedKWise.tabBase offHash (Succinct.qBits U N)
        (Succinct.hashB N) (totalMicroBits N) 3 + wIdx := by
      dsimp only [ReducedKWise.tabBase]; omega
    have ha_hi : ReducedKWise.tabBase offHash (Succinct.qBits U N)
        (Succinct.hashB N) (totalMicroBits N) 3 + wIdx < offLM U w N := by
      dsimp only [offLM, Succinct.hashSpace, ReducedKWise.tabBase, ReducedKWise.space]; omega
    rw [heq _ ha_lo ha_hi]
    exact htab1 wIdx hwIdx
  · let t := reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N)
    have hp : reducedPackShift t w ≤ 2 * reducedChunkBits t := reducedPackShift_le t w
    have hshr_lt : idx >>> reducedPackShift t w <
        ReducedKWise.tableWords w (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N) := by
      rw [Nat.shiftRight_eq_div_pow]
      dsimp only [ReducedKWise.tableWords, reducedTableWords, t] at hp ⊢
      rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hp]
      exact hidx
    have ha_lo : offHash ≤ ReducedKWise.tabBase offHash (Succinct.qBits U N)
        (Succinct.hashB N) (totalMicroBits N) 3 + (idx >>> reducedPackShift t w) := by
      dsimp only [ReducedKWise.tabBase]
      rw [Nat.add_assoc]
      exact Nat.le_add_right offHash _
    have ha_hi : ReducedKWise.tabBase offHash (Succinct.qBits U N)
        (Succinct.hashB N) (totalMicroBits N) 3 + (idx >>> reducedPackShift t w) <
        offLM U w N := by
      dsimp only [offLM, Succinct.hashSpace, ReducedKWise.tabBase, ReducedKWise.space]
      rw [Nat.add_assoc]
      exact Nat.add_lt_add_left (Nat.add_lt_add_left hshr_lt _) offHash
    rw [heq _ ha_lo ha_hi]
    exact htab2 idx hidx
  · have hpos := ReducedKWise.seedWords_pos (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3
    have ha_hi : offHash < offLM U w N := by
      dsimp only [offLM, Succinct.hashSpace, ReducedKWise.space]; omega
    rw [heq offHash le_rfl ha_hi]
    exact hseed0
  · let L := reducedLimbCount
      (reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N))
    have hlt_seed : 1 + (m.val + L * j.val) <
        ReducedKWise.seedWords (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N) 3 := by
      dsimp only [ReducedKWise.seedWords, L]
      have hj : j.val + 1 ≤ 3 := j.isLt
      have hm : m.val < L := m.isLt
      dsimp only [L] at hm
      have hmul : reducedLimbCount
          (reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N)) *
          (j.val + 1) ≤
          reducedLimbCount
          (reducedTrinomialStep (Succinct.qBits U N) (Succinct.hashB N) (totalMicroBits N)) * 3 :=
        Nat.mul_le_mul_left _ hj
      rw [Nat.mul_add, Nat.mul_one] at hmul
      omega
    have ha_lo : offHash ≤ offHash + 1 + (m.val + L * j.val) := by omega
    have ha_hi : offHash + 1 + (m.val + L * j.val) < offLM U w N := by
      dsimp only [offLM, Succinct.hashSpace, ReducedKWise.space]
      dsimp only [L] at hlt_seed ⊢
      omega
    rw [heq _ ha_lo ha_hi]
    exact hseed_limbs j m

/-- `FixedCoupled` depends only on `gmAtBit`, `lmAtBit`, `tdAtBit`, `dtAtBit`, and the dense items
`d < totalSlots N gm`. -/
theorem fixedCoupled_congr {U V w N : ℕ} {s_fix : Memory.State}
    {s₁ s₂ : BitMemory.State}
    (hcpl : FixedCoupled U V w N s_fix s₁)
    (hgm : gmAtBit U w N s₂.mem = gmAtBit U w N s₁.mem)
    (hlm : lmAtBit U w N s₂.mem = lmAtBit U w N s₁.mem)
    (htd : tdAtBit U w N s₂.mem = tdAtBit U w N s₁.mem)
    (hdt : dtAtBit U w N s₂.mem = dtAtBit U w N s₁.mem)
    (hitems : ∀ d < Succinct.totalSlots N (gmAtBit U w N s₁.mem),
      denseQuotAt U V w N s₂ d = denseQuotAt U V w N s₁ d ∧
      denseValAt U V w N s₂ d = denseValAt U V w N s₁ d) :
    FixedCoupled U V w N s_fix s₂ where
  gm_eq := hgm.trans hcpl.gm_eq
  lm_eq := hlm.trans hcpl.lm_eq
  win_inv := by rw [hgm, htd, hdt]; exact hcpl.win_inv
  td_lt i := by rw [htd]; exact hcpl.td_lt i
  dt_lt i := by rw [hdt]; exact hcpl.dt_lt i
  quot_eq d hd := by
    rw [hgm] at hd
    rw [(hitems d hd).1, hgm, hdt]
    exact hcpl.quot_eq d hd
  val_eq d hd := by
    rw [hgm] at hd
    rw [(hitems d hd).2, hgm, hdt]
    exact hcpl.val_eq d hd


/-- Updating only words `< 4` (header words `0..3`) preserves `FixedCoupled` when `0 < w`. -/
theorem fixedCoupled_of_ge_four_eq {U V w N : ℕ} (hw : 0 < w) {s_fix : Memory.State}
    {s₁ s₂ : BitMemory.State}
    (hcpl : FixedCoupled U V w N s_fix s₁)
    (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hge4 : ∀ a, 4 ≤ a → s₂.mem a = s₁.mem a) :
    FixedCoupled U V w N s_fix s₂ := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  refine fixedCoupled_congr hcpl ?_ ?_ ?_ ?_ (fun d _ => ⟨?_, ?_⟩)
  · funext i; unfold gmAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hge4 a (by
        have hlo := ha.1; unfold offGM offLM offHash at hlo; omega)) hi
    · rfl
  · funext ⟨c, j⟩; unfold lmAtBit
    split_ifs with hcj
    · exact readPacked_congr hw (fun a ha => hge4 a (by
        have hlo := ha.1; unfold offLMSub offLM offHash at hlo; omega)) hcj.2
    · rfl
  · funext i; unfold tdAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hge4 a (by
        have hlo := ha.1; unfold offTD offGM offLM offHash at hlo; omega)) hi
    · rfl
  · funext i; unfold dtAtBit
    split_ifs with hi
    · exact readPacked_congr hw (fun a ha => hge4 a (by
        have hlo := ha.1; unfold offDT offTD offGM offLM offHash at hlo; omega)) hi
    · rfl
  · unfold denseQuotAt BitMemory.State.getField
    refine readField_congr_words hw hqw fun k _ => ?_
    rw [Nat.zero_add]
    refine hge4 _ ((Nat.le_div_iff_mul_le hw).mpr ?_)
    have h4 : 4 ≤ epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
    have hmul : 4 * w ≤ epochMetaBits U w N := Nat.mul_le_mul_right w h4
    unfold itemQuotBitOff itemBitOff; omega
  · unfold denseValAt BitMemory.State.getField
    refine readField_congr_words hw hvw fun k _ => ?_
    rw [Nat.zero_add]
    refine hge4 _ ((Nat.le_div_iff_mul_le hw).mpr ?_)
    have h4 : 4 ≤ epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
    have hmul : 4 * w ≤ epochMetaBits U w N := Nat.mul_le_mul_right w h4
    unfold itemValBitOff itemBitOff; omega

/-- Uniform parameter-free `BitRAM.Code .standard 280` program synchronizing header word `mem 0`
to `Succinct.totalSlots N (gmAtBit U w N x.mem)` in `≤ 99` instructions. -/
@[expose]
def syncHdrCountRegCode : BitRAM.Code .standard 280 :=
  .seq (readGMConstRegCode 0 14)
  (.seq (.op (.const 13 0))
  (.seq (.branch (.eq 245 13)
          nopRegCode
          (.seq (readGMConstRegCode 1 15)
          (.seq (.op (.bin .mul 14 14 250))
                (.op (.bin .add 14 14 15)))))
  (.seq (.op (.const 13 0))
        (.op (.store 13 14)))))

theorem syncHdrCountRegCode_exec {U V w N : ℕ} {x : BitRAM.Data 280}
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : Fits w U)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hslot : Succinct.SlotStoreInv N (gmAtBit U w N x.mem))
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w syncHdrCountRegCode x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        y.mem 0 = Succinct.totalSlots N (gmAtBit U w N x.mem) ∧
        (∀ a, 1 ≤ a → y.mem a = x.mem a)) 99 := by
  set gm := gmAtBit U w N x.mem
  have h0_fit : Fits w 0 := fits_zero w
  have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hnU hU hv
  have hact := her.active hN_pos
  have h245 : x.regs 245 = bucketBits N := hact.1
  have h250 : x.regs 250 = slabSize N := hact.2.2.2.2.2.1
  have h4_le : 4 ≤ epochMetaWords U w N := by
    unfold epochMetaWords; split_ifs <;> omega
  have h1w_le : 1 * w ≤ x.bitSize :=
    (Nat.mul_le_mul_right w (by omega : 1 ≤ epochMetaWords U w N)).trans hsz
  have hadm0 : 0 < x.wordSize w := by
    have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
    exact Nat.pos_of_ne_zero fun hz => by rw [hz, Nat.zero_mul] at hcov; omega
  unfold syncHdrCountRegCode
  refine .seq (T₁ := 46) (T₂ := 53)
    (readGMConstRegCode_exec (by decide) (by decide) (by decide) hw hN_pos hnU hU hx her hsz)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_14, _⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  refine DemonicExecWithin.step_const (T := 52) h0_fit ?_
  set s1 := y1.set 13 0
  have hs1_wf : s1.WellFormed w := wf_set 13 hy1_wf h0_fit
  have hs1_er : EpochRegs U V w N s1 := hy1_er.set_of_outside (Or.inl (by decide)) 0
  have hs1_245 : s1.regs 245 = bucketBits N := (hs1_er.active hN_pos).1
  have hs1_14 : s1.regs 14 = gm 0 := by simp +decide [s1, BitRAM.Data.set, hy1_14, gm]
  have hbranch : BitRAM.DemonicExecWithin w
      (.branch (.eq 245 13)
        nopRegCode
        (.seq (readGMConstRegCode 1 15)
        (.seq (.op (.bin .mul 14 14 250))
              (.op (.bin .add 14 14 15))))) s1
      (fun y2 =>
        y2.toBitMemoryState = x.toBitMemoryState ∧
        y2.WellFormed w ∧
        EpochRegs U V w N y2 ∧
        y2.regs 14 = Succinct.totalSlots N gm) 50 := by
    by_cases hb0 : bucketBits N = 0
    · have hc : BitRAM.CondHolds (.eq 245 13) s1 := by
        change s1.regs 245 = s1.regs 13
        rw [hs1_245, hb0]
        simp +decide [s1, BitRAM.Data.set]
      refine .branch_pos (T₀ := 1) hc (nopRegCode_exec ?_) (by omega)
      refine ⟨hy1_st, hs1_wf, hs1_er, ?_⟩
      unfold Succinct.totalSlots; rw [ite_eq_left hb0]; exact hs1_14
    · have hb_pos : 0 < bucketBits N := Nat.pos_of_ne_zero hb0
      have hc : ¬BitRAM.CondHolds (.eq 245 13) s1 := by
        change s1.regs 245 ≠ s1.regs 13
        have h13 : s1.regs 13 = 0 := by simp +decide [s1, BitRAM.Data.set]
        rw [hs1_245, h13]
        exact hb0
      refine .branch_neg (T₀ := 48) hc ?_ (by omega)
      refine .seq (T₁ := 46) (T₂ := 2)
        (readGMConstRegCode_exec (by decide) (by decide) (by decide) hw hN_pos hnU hU hs1_wf hs1_er
          (by change epochMetaBits U w N ≤ y1.bitSize; rw [hy1_sz]; exact hsz))
        (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_15, hy2_regs⟩ => ?_) le_rfl
      have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
      have hy2_14 : y2.regs 14 = gm 0 := (hy2_regs 14 (by decide) (by decide)).trans hs1_14
      have hy2_15_eq : y2.regs 15 = gm 1 := by
        rw [hy2_15, show s1.mem = x.mem from hy1_mem]
      have hy2_250 : y2.regs 250 = slabSize N := (hy2_er.active hN_pos).2.2.2.2.2.1
      have htot_le : gm 0 * slabSize N + gm 1 ≤ N := hslot.multi_total_le hb_pos
      have hmul_fit : Fits w (gm 0 * slabSize N) := hfit_N _ (by omega)
      have htot_fit : Fits w (gm 0 * slabSize N + gm 1) := hfit_N _ (by omega)
      refine step_dExec_bin (v := gm 0 * slabSize N) (T := 1)
        (by simp +decide [BinOp.eval, hy2_14, hy2_250]) hmul_fit ?_
      refine dExec_bin (v := gm 0 * slabSize N + gm 1)
        (by simp +decide [BitRAM.Data.set, BinOp.eval, hy2_15_eq]) htot_fit ?_
      refine ⟨hy2_st_x,
        wf_set 14 (wf_set 14 hy2_wf hmul_fit) htot_fit,
        (hy2_er.set_of_outside (Or.inl (by decide)) _).set_of_outside (Or.inl (by decide)) _,
        ?_⟩
      unfold Succinct.totalSlots; rw [ite_eq_right hb0]
      simp +decide [BitRAM.Data.set]
  refine .seq (T₁ := 50) (T₂ := 2) hbranch
    (fun y2 ⟨hy2_st, hy2_wf, hy2_er, hy2_14⟩ => ?_) le_rfl
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st
  have htot_fit : Fits w (Succinct.totalSlots N gm) := hy2_14 ▸ hy2_wf.regs_fits 14
  refine DemonicExecWithin.step_const (T := 1) h0_fit ?_
  set s2 := y2.set 13 0
  have hs2_wf : s2.WellFormed w := wf_set 13 hy2_wf h0_fit
  have hs2_er : EpochRegs U V w N s2 := hy2_er.set_of_outside (Or.inl (by decide)) 0
  have hadm_s2 : s2.regs 13 < s2.wordSize w := by
    change 0 < y2.bitSize ⌈/⌉ w
    rw [hy2_sz]
    exact hadm0
  refine DemonicExecWithin.store hadm_s2 ?_
  have hs2_14 : s2.regs 14 = Succinct.totalSlots N gm := by
    simp +decide [s2, BitRAM.Data.set, hy2_14]
  have hs2_13 : s2.regs 13 = 0 := by simp +decide [s2, BitRAM.Data.set]
  rw [hs2_13, hs2_14]
  refine ⟨wf_write_of_word_lt hw hs2_wf htot_fit
      (by change 1 * w ≤ y2.bitSize; rw [hy2_sz]; exact h1w_le),
    hs2_er.write 0 _,
    hy2_sz,
    by simp +decide [BitRAM.Data.write],
    fun a ha => by
      have hne : a ≠ 0 := by omega
      change Function.update y2.mem 0 (Succinct.totalSlots N gm) a = x.mem a
      rw [Function.update_of_ne hne, hy2_mem]⟩

/-! ## Section 3: Uniform parameter-free empty-dictionary initialization (`initEmptyRegCode`) -/

/-- Fixed parameter-free `BitRAM.Code .standard 280` program initializing an empty bit-resizable
dictionary (`N = 0`, `Dynamic.empty U`) from `x.bitSize = 0`, given `r240 = U` and `r241 = V`:
computes `keyBits U` into `r242` and `r244`, `valBits V` into `r243`, grows `bitSize` by `4 * w`
bits under demonic `.grow`, and writes header words `mem 0..3 = (0, 0, itemBits U V 0, 4 * w)`. -/
@[expose]
def initEmptyRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.copy 0 240))
  (.seq (BitRAM.Code.embed12 (by decide) clog2BitCode)
  (.seq (.op (.copy 242 1))
  (.seq (.op (.copy 244 1))
  (.seq (.op (.copy 0 241))
  (.seq (BitRAM.Code.embed12 (by decide) clog2BitCode)
  (.seq (.op (.copy 243 1))
  (.seq (.op (.bin .add 14 242 243))
  (.seq (.op (.width 15))
  (.seq (.op (.const 13 4))
  (.seq (.op (.bin .mul 16 13 15))
  (.seq (.grow 17 16)
  (.seq (.op (.const 13 0))
  (.seq (.op (.store 13 13))
  (.seq (.op (.const 12 1))
  (.seq (.op (.store 12 13))
  (.seq (.op (.const 12 2))
  (.seq (.op (.store 12 14))
  (.seq (.op (.const 12 3))
        (.op (.store 12 16))))))))))))))))))))


/-- Executing `initEmptyRegCode` from any well-formed state `x : BitRAM.Data 280` with
`x.bitSize = 0`, `x.regs 240 = U`, and `x.regs 241 = V` (`0 < w`, `Fits w U`, `Fits w V`,
`Fits w (4 * w)`) takes at most `8 * w + 37` instructions under demonic `.grow` and establishes
`EpochDictInv U V w 0 θ₀ (Dynamic.empty U) ⟨fun _ => 0, 0⟩ y` with `y.bitSize = 4 * w` and
`inEpochPotential U V w 0 ⟨fun _ => 0, 0⟩ = 0`. -/
theorem initEmptyRegCode_exec {U V w : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V) (hfit0 : Fits w (4 * w))
    (θ₀ : Succinct.QuotHashSeed U 0)
    {x : BitRAM.Data 280} (hx : x.WellFormed w) (hx_sz : x.bitSize = 0)
    (hr240 : x.regs 240 = U) (hr241 : x.regs 241 = V) :
    BitRAM.DemonicExecWithin w initEmptyRegCode x
      (fun y =>
        EpochDictInv U V w 0 θ₀ (Dynamic.empty U) ⟨fun _ => 0, 0⟩ y ∧
        y.bitSize = 4 * w ∧
        inEpochPotential U V w 0 ⟨fun _ => 0, 0⟩ = 0) (8 * w + 37) := by
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := hfit0.of_le (by omega)
  have hfit_2 : Fits w 2 := hfit0.of_le (by omega)
  have hfit_3 : Fits w 3 := hfit0.of_le (by omega)
  have hfit_4 : Fits w 4 := hfit0.of_le (by omega)
  have hfit_w : Fits w w := fits_self w
  have hkb_le : keyBits U ≤ w := by
    unfold keyBits
    exact Nat.clog_le_iff_le_pow (by decide) |>.mpr hU.le
  have hvb_le : valBits V ≤ w := valBits_le_of_le_pow hV.le
  have hfit_kb : Fits w (keyBits U) := hfit_w.of_le hkb_le
  have hfit_vb : Fits w (valBits V) := hfit_w.of_le hvb_le
  have hfit_ib : Fits w (keyBits U + valBits V) := hfit0.of_le (by omega)
  unfold initEmptyRegCode
  refine step_dExec_copy (v := U) (T := 8 * w + 36) hr240 ?_
  set s0 := x.set 0 U
  have hs0_wf : s0.WellFormed w := wf_set 0 hx hU
  have hclogU := DemonicExecWithin.embed12 (by decide)
    (clog2BitCode_exec hw (x := s0.comap (embedFin12 (by decide)))
      (by simp +decide [s0, BitRAM.Data.comap, embedFin12, BitRAM.Data.set, hU]))
  refine .seq (T₁ := 4 * w + 8) (T₂ := 4 * w + 28)
    (dExec_with_fits hclogU hs0_wf.regs_fits hs0_wf.mem_wf.mem_fits)
    (fun y1 ⟨⟨⟨hy1_1, _, hy1_mem12, hy1_sz12⟩, hy1_hi⟩, hy1_rfits, _⟩ => ?_) (by omega)
  have hy1_st : y1.toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact congrFun hy1_mem12 a
    · exact hy1_sz12
  have hy1_wf : y1.WellFormed w := ⟨hy1_rfits, hy1_st ▸ hx.mem_wf⟩
  have hy1_kb : y1.regs 1 = keyBits U := by
    simpa +decide [s0, BitRAM.Data.comap, embedFin12, BitRAM.Data.set, keyBits] using hy1_1
  have hy1_241 : y1.regs 241 = V :=
    (hy1_hi 241 (by decide)).trans (by simp +decide [s0, BitRAM.Data.set, hr241])
  have hy1_240 : y1.regs 240 = U :=
    (hy1_hi 240 (by decide)).trans (by simp +decide [s0, BitRAM.Data.set, hr240])
  refine step_dExec_copy (v := keyBits U) (T := 4 * w + 27) hy1_kb ?_
  refine step_dExec_copy (v := keyBits U) (T := 4 * w + 26)
    (by simp +decide [BitRAM.Data.set, hy1_kb]) ?_
  refine step_dExec_copy (v := V) (T := 4 * w + 25)
    (by simp +decide [BitRAM.Data.set, hy1_241]) ?_
  set s1 := ((y1.set 242 (keyBits U)).set 244 (keyBits U)).set 0 V
  have hs1_wf : s1.WellFormed w :=
    wf_set 0 (wf_set 244 (wf_set 242 hy1_wf hfit_kb) hfit_kb) hV
  have hclogV := DemonicExecWithin.embed12 (by decide)
    (clog2BitCode_exec hw (x := s1.comap (embedFin12 (by decide)))
      (by simp +decide [s1, BitRAM.Data.comap, embedFin12, BitRAM.Data.set, hV]))
  refine .seq (T₁ := 4 * w + 8) (T₂ := 17)
    (dExec_with_fits hclogV hs1_wf.regs_fits hs1_wf.mem_wf.mem_fits)
    (fun y2 ⟨⟨⟨hy2_1, _, hy2_mem12, hy2_sz12⟩, hy2_hi⟩, hy2_rfits, _⟩ => ?_) (by omega)
  have hy2_st : y2.toBitMemoryState = x.toBitMemoryState := by
    ext a
    · exact (congrFun hy2_mem12 a).trans (congrArg (fun z => z.mem a) hy1_st)
    · exact hy2_sz12.trans (congrArg BitMemory.State.bitSize hy1_st)
  have hy2_wf : y2.WellFormed w := ⟨hy2_rfits, hy2_st ▸ hx.mem_wf⟩
  have hy2_vb : y2.regs 1 = valBits V := by
    simpa +decide [s1, BitRAM.Data.comap, embedFin12, BitRAM.Data.set, valBits] using hy2_1
  have hy2_240 : y2.regs 240 = U :=
    (hy2_hi 240 (by decide)).trans (by simp +decide [s1, BitRAM.Data.set, hy1_240])
  have hy2_241 : y2.regs 241 = V :=
    (hy2_hi 241 (by decide)).trans (by simp +decide [s1, BitRAM.Data.set, hy1_241])
  have hy2_242 : y2.regs 242 = keyBits U :=
    (hy2_hi 242 (by decide)).trans (by simp +decide [s1, BitRAM.Data.set])
  have hy2_244 : y2.regs 244 = keyBits U :=
    (hy2_hi 244 (by decide)).trans (by simp +decide [s1, BitRAM.Data.set])
  refine step_dExec_copy (v := valBits V) (T := 16) hy2_vb ?_
  refine step_dExec_bin (v := keyBits U + valBits V) (T := 15)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, hy2_242]) hfit_ib ?_
  refine DemonicExecWithin.step_width (T := 14) ?_
  refine DemonicExecWithin.step_const (T := 13) hfit_4 ?_
  refine step_dExec_bin (v := 4 * w) (T := 12)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) hfit0 ?_
  set s2 := ((((y2.set 243 (valBits V)).set 14 (keyBits U + valBits V)).set 15 w).set 13 4).set
    16 (4 * w)
  have hs2_wf : s2.WellFormed w :=
    wf_set 16 (wf_set 13 (wf_set 15 (wf_set 14 (wf_set 243 hy2_wf hfit_vb) hfit_ib) hfit_w)
      hfit_4) hfit0
  have hs2_sz : s2.bitSize = 0 := (congrArg BitMemory.State.bitSize hy2_st).trans hx_sz
  have hs2_16 : s2.regs 16 = 4 * w := by simp +decide [s2, BitRAM.Data.set]
  have hgrow_fits : Fits w (s2.bitSize + s2.regs 16) := by
    rw [hs2_sz, hs2_16, Nat.zero_add]; exact hfit0
  have hceil4 : (s2.regs 16) ⌈/⌉ w ≤ 4 := by
    rw [hs2_16, Nat.ceilDiv_le_iff hw]
  have hcost_grow : max 1 ((s2.regs 16) ⌈/⌉ w) ≤ 4 := max_le (by omega) hceil4
  refine .seq
    (Q := fun y3 : BitRAM.Data 280 =>
      ∃ s_mem : BitMemory.State,
        BitMemory.dirtyStep w s2.toBitMemoryState (.grow (4 * w)) s_mem 0 ∧
        y3 = ⟨Function.update s2.regs 17 0, s_mem.mem, s_mem.bitSize⟩)
    (T₁ := 4) (T₂ := 8)
    (.grow hgrow_fits hcost_grow fun s_mem hs_mem => by
      rw [hs2_sz, hs2_16] at hs_mem
      refine ⟨s_mem, hs_mem, ?_⟩
      rw [hs2_sz])
    (fun y3 ⟨s_mem, hs_mem, hy3_eq⟩ => ?_) (by omega)
  subst hy3_eq
  have hs_mem_wf : s_mem.WellFormed w :=
    BitMemory.wellFormed_dirtyStep hw hs2_wf.mem_wf
      (show BitMemory.valid w s2.toBitMemoryState (.grow (4 * w)) by
        change Fits w (s2.bitSize + 4 * w); rw [hs2_sz, Nat.zero_add]; exact hfit0) hs_mem
  have hs_mem_sz : s_mem.bitSize = 4 * w := by
    have h1 : s_mem.bitSize = s2.bitSize + 4 * w := hs_mem.1
    rw [hs2_sz, Nat.zero_add] at h1
    exact h1
  set y3 : BitRAM.Data 280 := ⟨Function.update s2.regs 17 0, s_mem.mem, s_mem.bitSize⟩
  have hy3_wf : y3.WellFormed w := by
    refine ⟨fun i => ?_, hs_mem_wf⟩
    by_cases hi : i = 17
    · subst hi; simp [y3, hfit_0]
    · simpa [y3, Function.update_of_ne hi] using hs2_wf.regs_fits i
  have hy3_ws : y3.wordSize w = 4 := by
    change s_mem.bitSize ⌈/⌉ w = 4
    rw [hs_mem_sz]
    apply le_antisymm
    · exact (Nat.ceilDiv_le_iff hw).mpr le_rfl
    · by_contra hlt
      have hle3 : (4 * w) ⌈/⌉ w ≤ 3 := by omega
      have hmul := (Nat.ceilDiv_le_iff hw).mp hle3
      omega
  have hy3_14 : y3.regs 14 = itemBits U V 0 := by
    have hq0 : quotientBits U 0 = keyBits U := by
      unfold quotientBits bucketBits; simp
    simp +decide [y3, s2, BitRAM.Data.set, itemBits, hq0]
  have hy3_16 : y3.regs 16 = 4 * w := by simp +decide [y3, s2, BitRAM.Data.set]
  have hy3_er : EpochRegs U V w 0 y3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, fun h => by omega⟩
    · simp +decide [y3, s2, BitRAM.Data.set, hy2_240]
    · simp +decide [y3, s2, BitRAM.Data.set, hy2_241]
    · simp +decide [y3, s2, BitRAM.Data.set, hy2_242]
    · simp +decide [y3, s2, BitRAM.Data.set]
    · have hq0 : quotientBits U 0 = keyBits U := by unfold quotientBits bucketBits; simp
      simp +decide [y3, s2, BitRAM.Data.set, hy2_244, hq0]
  refine DemonicExecWithin.step_const (T := 7) hfit_0 ?_
  set z0 := y3.set 13 0
  have hz0_wf : z0.WellFormed w := wf_set 13 hy3_wf hfit_0
  have hz0_er : EpochRegs U V w 0 z0 := hy3_er.set_of_outside (Or.inl (by decide)) 0
  have hz0_adm : z0.regs 13 < z0.wordSize w := by
    change 0 < y3.wordSize w; rw [hy3_ws]; decide
  refine DemonicExecWithin.step_store (T := 6) hz0_adm ?_
  set z1 := z0.write (z0.regs 13) (z0.regs 13)
  have hz1_wf : z1.WellFormed w :=
    wf_write_of_word_lt hw hz0_wf hfit_0 (by change 1 * w ≤ s_mem.bitSize; omega)
  have hz1_er : EpochRegs U V w 0 z1 := hz0_er.write _ _
  refine DemonicExecWithin.step_const (T := 5) hfit_1 ?_
  set z2 := z1.set 12 1
  have hz2_wf : z2.WellFormed w := wf_set 12 hz1_wf hfit_1
  have hz2_er : EpochRegs U V w 0 z2 := hz1_er.set_of_outside (Or.inl (by decide)) 1
  have hz2_adm : z2.regs 12 < z2.wordSize w := by
    change 1 < y3.wordSize w; rw [hy3_ws]; decide
  refine DemonicExecWithin.step_store (T := 4) hz2_adm ?_
  set z3 := z2.write (z2.regs 12) (z2.regs 13)
  have hz3_wf : z3.WellFormed w :=
    wf_write_of_word_lt hw hz2_wf hfit_0 (by change 2 * w ≤ s_mem.bitSize; omega)
  have hz3_er : EpochRegs U V w 0 z3 := hz2_er.write _ _
  refine DemonicExecWithin.step_const (T := 3) hfit_2 ?_
  set z4 := z3.set 12 2
  have hz4_wf : z4.WellFormed w := wf_set 12 hz3_wf hfit_2
  have hz4_er : EpochRegs U V w 0 z4 := hz3_er.set_of_outside (Or.inl (by decide)) 2
  have hz4_adm : z4.regs 12 < z4.wordSize w := by
    change 2 < y3.wordSize w; rw [hy3_ws]; decide
  refine DemonicExecWithin.step_store (T := 2) hz4_adm ?_
  set z5 := z4.write (z4.regs 12) (z4.regs 14)
  have hz5_14 : z4.regs 14 = itemBits U V 0 := by
    simpa +decide [z4, z3, z2, z1, z0, BitRAM.Data.set, BitRAM.Data.write] using hy3_14
  have hz5_wf : z5.WellFormed w :=
    wf_write_of_word_lt hw hz4_wf (hz5_14.symm ▸ hfit_ib) (by change 3 * w ≤ s_mem.bitSize; omega)
  have hz5_er : EpochRegs U V w 0 z5 := hz4_er.write _ _
  refine DemonicExecWithin.step_const (T := 1) hfit_3 ?_
  set z6 := z5.set 12 3
  have hz6_wf : z6.WellFormed w := wf_set 12 hz5_wf hfit_3
  have hz6_er : EpochRegs U V w 0 z6 := hz5_er.set_of_outside (Or.inl (by decide)) 3
  have hz6_adm : z6.regs 12 < z6.wordSize w := by
    change 3 < y3.wordSize w; rw [hy3_ws]; decide
  refine DemonicExecWithin.store hz6_adm ?_
  set z7 := z6.write (z6.regs 12) (z6.regs 16)
  have hz6_16 : z6.regs 16 = 4 * w := by
    simpa +decide [z6, z5, z4, z3, z2, z1, z0, BitRAM.Data.set, BitRAM.Data.write] using hy3_16
  have hz7_wf : z7.WellFormed w :=
    wf_write_of_word_lt hw hz6_wf (hz6_16.symm ▸ hfit0) (by change 4 * w ≤ s_mem.bitSize; omega)
  have hz7_er : EpochRegs U V w 0 z7 := hz6_er.write _ _
  have hdom0 : (Dynamic.dom (Dynamic.empty U)).card = 0 := by
    have heq : Dynamic.dom (Dynamic.empty U) = ∅ := by ext k; simp [Dynamic.empty]
    rw [heq, Finset.card_empty]
  have hd0 : dictBitSize U V w 0 0 = 4 * w := by
    unfold dictBitSize epochMetaBits epochMetaWords; simp
  have hm0 : epochMetaBits U w 0 = 4 * w := by
    unfold epochMetaBits epochMetaWords; simp
  have hval_emp : Dynamic.ValuesBounded V (Dynamic.empty U) :=
    fun _ _ h => by simp [Dynamic.empty, Dictionary.empty] at h
  refine ⟨⟨hz7_wf, hz7_er, Nat.zero_le U, by rw [hdom0], hval_emp, hd0 ▸ hfit0,
    by change s_mem.bitSize = _; rw [hdom0, hd0, hs_mem_sz],
    by rw [hdom0]; simp +decide [z7, z6, z5, z4, z3, z2, z1, z0,
      BitRAM.Data.set, BitRAM.Data.write],
    by simp +decide [z7, z6, z5, z4, z3, z2, z1, z0, BitRAM.Data.set, BitRAM.Data.write],
    by simp +decide [z7, z6, z5, z4, z3, z2, z1, z0, BitRAM.Data.set, BitRAM.Data.write, hy3_14],
    by rw [hm0]; simp +decide [z7, z6, z5, z4, z3, z2, z1, z0, BitRAM.Data.set, BitRAM.Data.write,
      hy3_16],
    fun h => by omega⟩, hs_mem_sz, rfl⟩

/-! ## Section 4: Unified in-epoch operation programs (`query`, `insert`, `delete`, dispatch) -/

theorem four_le_wordSize_of_epochDictInv {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_fix : Memory.State} {x : BitRAM.Data 280}
    (hw : 0 < w) (hinv : EpochDictInv U V w N θ s_abs s_fix x) :
    4 ≤ x.wordSize w := by
  have h4_meta : 4 ≤ epochMetaWords U w N := by
    unfold epochMetaWords; split_ifs <;> omega
  have h4w : 4 * w ≤ x.bitSize := by
    rw [hinv.bitSize_eq]
    exact (Nat.mul_le_mul_right w h4_meta).trans (Nat.le_add_right _ _)
  have hcov : x.bitSize ≤ x.wordSize w * w := Nat.le_ceilDiv_mul hw
  by_contra hlt
  have hle3 : x.wordSize w ≤ 3 := by omega
  have hmul : x.wordSize w * w ≤ 3 * w := Nat.mul_le_mul_right w hle3
  omega

/-- Uniform parameter-free `BitRAM.Code .standard 280` program executing a dictionary `query`
in any `EpochDictInv` state (both `N = 0` and `0 < N`), given `r270 = u.val`. -/
@[expose]
def queryOpRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 1))
  (.seq (.op (.load 13 12))
  (.seq (.op (.const 12 0))
  (.branch (.eq 13 12)
    (.seq (.op (.const 0 0)) (.op (.const 1 0)))
    queryRegCode)))

/-- Uniform parameter-free `BitRAM.Code .standard 280` program executing an in-epoch `insert`
followed by header-count synchronization (`mem 0`), given `r270 = u.val` and `r274 = v`. -/
@[expose]
def inEpochInsertOpRegCode : BitRAM.Code .standard 280 :=
  .seq inEpochInsertRegCode syncHdrCountRegCode

/-- Uniform parameter-free `BitRAM.Code .standard 280` program executing an in-epoch `delete`
(both `N = 0` and `0 < N`) followed by header-count synchronization (`mem 0`), given
`r270 = u.val`. -/
@[expose]
def inEpochDeleteOpRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 1))
  (.seq (.op (.load 13 12))
  (.seq (.op (.const 12 0))
  (.branch (.eq 13 12)
    nopRegCode
    (.seq inEpochDeleteRegCode syncHdrCountRegCode))))

/-- Fixed uniform parameter-free `BitRAM.Code .standard 280` program dispatching `query`
(`r278 = 0`), `insert` (`r278 = 1`), and `delete` (`r278 = 2`). -/
@[expose]
def inEpochStepRegCode : BitRAM.Code .standard 280 :=
  .seq (.op (.const 12 0))
  (.branch (.eq 278 12)
    queryOpRegCode
    (.seq (.op (.const 12 1))
    (.branch (.eq 278 12)
      inEpochInsertOpRegCode
      inEpochDeleteOpRegCode)))

/-- Deterministic per-step amortized instruction overhead for `inEpochStepRegCode`. -/
@[expose]
noncomputable def inEpochStepOverhead (U N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (op : Dynamic.Op U) : ℕ :=
  292700 + 350 * epochProbeExcess U N θ s_abs (opKey op)

theorem queryOpRegCode_exec {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    (u : Fin U) (hr270 : x.regs 270 = u.val) :
    ∃ T : ℕ,
      BitRAM.DemonicExecWithin w queryOpRegCode x
        (fun y =>
          EpochDictInv U V w N θ s_abs s_fix y ∧
          decodeQueryRegs y.regs = s_abs u) T ∧
      T ≤ 143692 + 350 * epochProbeExcess U N θ s_abs u := by
  have h4_ws : 4 ≤ x.wordSize w := four_le_wordSize_of_epochDictInv hw hinv
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  unfold queryOpRegCode
  by_cases hN0 : N = 0
  · subst hN0
    refine ⟨6, ?_, by omega⟩
    refine DemonicExecWithin.step_const (T := 5) hfit_1 ?_
    set s0 := x.set 12 1
    have hs0_adm : s0.regs 12 < s0.wordSize w := by
      change 1 < x.wordSize w; omega
    refine DemonicExecWithin.step_load (T := 4) hs0_adm ?_
    set s1 := s0.set 13 (s0.mem (s0.regs 12))
    refine DemonicExecWithin.step_const (T := 3) hfit_0 ?_
    set s2 := s1.set 12 0
    have hc : BitRAM.CondHolds (.eq 13 12) s2 := by
      change x.mem 1 = 0
      exact hinv.hdr_cap
    refine .branch_pos (T₀ := 2) hc ?_ (by omega)
    refine DemonicExecWithin.step_const (T := 1) hfit_0 ?_
    refine DemonicExecWithin.const hfit_0 ?_
    set y := (s2.set 0 0).set 1 0
    have hy_wf : y.WellFormed w :=
      wf_set 1 (wf_set 0 (wf_set 12 (wf_set 13 (wf_set 12 hinv.wf hfit_1)
        (by change Fits w (x.mem 1); rw [hinv.hdr_cap]; exact hfit_0)) hfit_0) hfit_0) hfit_0
    have hy_er : EpochRegs U V w 0 y :=
      ((((hinv.epoch_regs.set_of_outside (Or.inl (by decide)) 1).set_of_outside
        (Or.inl (by decide)) _).set_of_outside (Or.inl (by decide)) 0).set_of_outside
        (Or.inl (by decide)) 0).set_of_outside (Or.inl (by decide)) 0
    have hs_none : s_abs u = none := by
      by_contra hne
      have his : (s_abs u).isSome := Option.ne_none_iff_isSome.mp hne
      have hmem : u ∈ Dynamic.dom s_abs := by simp [Dynamic.dom, his]
      have hpos : 0 < (Dynamic.dom s_abs).card := Finset.card_pos.mpr ⟨u, hmem⟩
      have := hinv.card_le
      omega
    refine ⟨⟨hy_wf, hy_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
      hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
      hinv.active⟩, ?_⟩
    rw [hs_none]
    simp +decide [y, decodeQueryRegs, BitRAM.Data.set]
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
    obtain ⟨hdict, hcpl, hhash⟩ := hinv.active hN_pos
    obtain ⟨L, hb_inv⟩ := hdict.hbucket
    set h1 := Succinct.hValOfSeed U N θ
    set q := keyQuotient (bucketBits N) u.val
    set b := feistelBucket (bucketBits N) h1 u.val
    set m := Succinct.mOfSeed U N θ q
    set gm := gmAtBit U w N x.mem
    have hb_lt : b < numBuckets N := feistelBucket_lt (bucketBits N) h1 u.val
    have hm_lt : m < numMicroPerBucket N := Succinct.mOfSeed_lt U N θ q
    have hfit_meta : Fits w (epochMetaWords U w N) :=
      hinv.fit_cap.of_le ((Nat.le_mul_of_pos_right _ hw).trans (Nat.le_add_right _ _))
    have hrep_bit : BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
        (Succinct.bucketMapOfState U N h1 s_abs) x.toBitMemoryState :=
      bucketRepInv_of_fixedCoupled hb_inv hcpl
    have hprobe := (chain_and_overflow_le_probeExcess_rep θ hrep_bit u).2.2.1
    set T_q := 142987 + 350 * (L b m).length + 287 * (Succinct.bCount N gm b - effBucketCap N)
    refine ⟨T_q + 5, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := T_q + 4) hfit_1 ?_
      set s0 := x.set 12 1
      have hs0_adm : s0.regs 12 < s0.wordSize w := by
        change 1 < x.wordSize w; omega
      refine DemonicExecWithin.step_load (T := T_q + 3) hs0_adm ?_
      set s1 := s0.set 13 (s0.mem (s0.regs 12))
      refine DemonicExecWithin.step_const (T := T_q + 2) hfit_0 ?_
      set s2 := s1.set 12 0
      have hc : ¬BitRAM.CondHolds (.eq 13 12) s2 := by
        change x.mem 1 ≠ 0
        rw [hinv.hdr_cap]
        exact hN0
      have hs2_wf : s2.WellFormed w :=
        wf_set 12 (wf_set 13 (wf_set 12 hinv.wf hfit_1)
          (by change Fits w (x.mem 1); exact hinv.wf.mem_wf.mem_fits 1)) hfit_0
      have hs2_er : EpochRegs U V w N s2 :=
        ((hinv.epoch_regs.set_of_outside (Or.inl (by decide)) 1).set_of_outside
          (Or.inl (by decide)) _).set_of_outside (Or.inl (by decide)) 0
      have hs2_270 : s2.regs 270 = u.val := by
        simp +decide [s2, s1, s0, BitRAM.Data.set, hr270]
      have hgm : gmAtBit U w N x.mem = _ := hcpl.gm_eq
      have hs2_sz : dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N s2.mem)) ≤
          s2.bitSize := by
        change dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem)) ≤ x.bitSize
        rw [hgm, hdict.htot, hinv.bitSize_eq]
      refine .branch_neg (T₀ := T_q) hc ?_ (by omega)
      refine (queryRegCode_exec (L := L b m) (x := s2)
        hw hN_pos hinv.cap_le hU hV.le hfit_meta θ u.isLt hs2_wf hs2_er
        hinv.hdr_cap hinv.hdr_itemBits hinv.hdr_metaBits hs2_sz hhash
        hrep_bit.hslot hrep_bit.htd
        (hrep_bit.hchains.1 b hb_lt m hm_lt)
        (fun j hj => ((hrep_bit.hchain_mem b hb_lt m hm_lt j).mp hj).1)
        hs2_270).mono (fun y ⟨hy_st, hy_wf, hy_er, hy_res, _⟩ => ?_) le_rfl
      have hy_mem : y.mem = x.mem := congrArg BitMemory.State.mem hy_st
      have hy_sz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy_st
      have hy_inv : EpochDictInv U V w N θ s_abs s_fix y :=
        ⟨hy_wf, hy_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
          hy_sz.trans hinv.bitSize_eq,
          (congrFun hy_mem 0).trans hinv.hdr_count,
          (congrFun hy_mem 1).trans hinv.hdr_cap,
          (congrFun hy_mem 2).trans hinv.hdr_itemBits,
          (congrFun hy_mem 3).trans hinv.hdr_metaBits,
          fun hp => by
            have hact := hinv.active hp
            exact ⟨hact.1, hy_st.symm ▸ hact.2.1, hy_mem.symm ▸ hact.2.2⟩⟩
      refine ⟨hy_inv, ?_⟩
      have hB_eq : Succinct.bucketMapOfState U N h1 s_abs b q = s_abs u :=
        Succinct.bucketMapOfState_feistelBucket hinv.cap_le h1 s_abs u
      classical
      change (if (∃ j ∈ L b m, virtualQuotAt U V w N x.toBitMemoryState
            (Succinct.slotOf N gm b j) = q) ∨
          (∃ j, effBucketCap N ≤ j ∧ j < Succinct.bCount N gm b ∧
            virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b j) = q) then
        y.regs 0 = 1 ∧ y.regs 33 < Succinct.bCount N gm b ∧
        (y.regs 33 ∈ L b m ∨ effBucketCap N ≤ y.regs 33) ∧
        virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)) = q ∧
        y.regs 1 = virtualValAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33))
      else y.regs 0 = 0 ∧ y.regs 1 = 0) at hy_res
      split_ifs at hy_res with hex
      · obtain ⟨hy0, hj_lt, _, hq_eq, hy1_eq⟩ := hy_res
        have hsome := hrep_bit.hmap_some b hb_lt (y.regs 33) hj_lt
        change Succinct.bucketMapOfState U N h1 s_abs b
            (virtualQuotAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33))) =
          some (virtualValAt U V w N x.toBitMemoryState (Succinct.slotOf N gm b (y.regs 33)))
          at hsome
        rw [hq_eq, hB_eq, ← hy1_eq] at hsome
        simp [decodeQueryRegs, hy0, hsome.symm]
      · obtain ⟨hy0, _⟩ := hy_res
        have hiff := searchBucket_cond_iff hb_inv hcpl hb_lt hm_lt (q := q)
        have hno_fix : ¬∃ j < Succinct.bCount N
            (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem) b,
            Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
              (Succinct.slotOf N (Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem)
                b j) = q :=
          mt hiff.mpr hex
        have hnot_some : ¬(s_abs u).isSome := by
          rw [← hB_eq]; exact mt (hb_inv.hmap_dom b hb_lt q).mp hno_fix
        have hnone : s_abs u = none := Option.not_isSome_iff_eq_none.mp hnot_some
        simp [decodeQueryRegs, hy0, hnone]
    · change (L b m).length + (Succinct.bCount N gm b - effBucketCap N) ≤
        2 + epochProbeExcess U N θ s_abs u at hprobe
      dsimp only [T_q]
      omega

theorem inEpochInsertOpRegCode_exec {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    (u : Fin U) (v_new : ℕ) (hvalid : (Dynamic.spec U V N).valid s_abs (.insert u v_new))
    (hr270 : x.regs 270 = u.val) (hr274 : x.regs 274 = v_new) :
    ∃ (s_fix' : Memory.State) (T : ℕ),
      BitRAM.DemonicExecWithin w inEpochInsertOpRegCode x
        (fun y =>
          EpochDictInv U V w N θ (Function.update s_abs u (some v_new)) s_fix' y) T ∧
      T + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + 147992 +
          350 * epochProbeExcess U N θ s_abs u := by
  have hN_pos : 0 < N := by
    rcases hvalid.1 with hlt | his
    · omega
    · have hmem : u ∈ Dynamic.dom s_abs := Dictionary.mem_dom_iff_isSome.mpr his
      have hpos : 0 < (Dynamic.dom s_abs).card := Finset.card_pos.mpr ⟨u, hmem⟩
      have := hinv.card_le
      omega
  have hN0 : N ≠ 0 := Nat.ne_of_gt hN_pos
  obtain ⟨hdict, hcpl, hhash⟩ := hinv.active hN_pos
  have hgm_x : gmAtBit U w N x.mem = _ := hcpl.gm_eq
  obtain ⟨hwf, henv, _⟩ :=
    dictEnv_of_fits_dictBitSize hw hN_pos hinv.cap_le hU hV.le hinv.fit_cap
  have hspec := Succinct.insertWithHashProg_dict_spec hwf henv θ hdict u v_new hvalid
  dsimp only at hspec
  obtain ⟨_, _, _, hdict', _⟩ := hspec
  set h_q := Succinct.hValOfSeed U N θ (keyQuotient (bucketBits N) u.val)
  set prog := Succinct.insertWithHashProg U V w N (((0, u.val), v_new), h_q)
  set s_fix' := (Memory.spec 0).clientState s_fix prog
  have hexec_ins := inEpochInsertRegCode_exec hwf henv hN_pos θ hdict u v_new hvalid
    hinv.wf hinv.epoch_regs hcpl hhash hinv.hdr_cap hinv.hdr_itemBits hinv.hdr_metaBits
    (by rw [hgm_x, hdict.htot, hinv.bitSize_eq]) hinv.fit_cap hr270 hr274
  dsimp only at hexec_ins
  obtain ⟨T₁, hExec₁, hT₁⟩ := hexec_ins
  obtain ⟨L', hb_inv'⟩ := hdict'.hbucket
  refine ⟨s_fix', T₁ + 99, ?_, ?_⟩
  · unfold inEpochInsertOpRegCode
    refine .seq (T₁ := T₁) (T₂ := 99) hExec₁
      (fun y1 ⟨hy1_wf, hy1_er, hy1_sz, hy1_cpl, hy1_low⟩ => ?_) le_rfl
    have hgm_y1 : gmAtBit U w N y1.mem = _ := hy1_cpl.gm_eq
    have hslot_y1 : Succinct.SlotStoreInv N (gmAtBit U w N y1.mem) := by
      rw [hgm_y1]; exact hb_inv'.hslot
    have hsz_meta_y1 : epochMetaBits U w N ≤ y1.bitSize := by
      rw [hy1_sz]; exact Nat.le_add_right _ _
    refine (syncHdrCountRegCode_exec hw hN_pos hinv.cap_le hU hy1_wf hy1_er hslot_y1
      hsz_meta_y1).mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_m0, hy_ge1⟩ => ?_) le_rfl
    have h1_lt : 1 < offLM U w N := by unfold offLM offHash; omega
    have h2_lt : 2 < offLM U w N := by unfold offLM offHash; omega
    have h3_lt : 3 < offLM U w N := by unfold offLM offHash; omega
    have hcard' : (Dynamic.dom (Function.update s_abs u (some v_new))).card ≤ N :=
      Dynamic.card_dom_step_le_of_valid (V := V) (o := .insert u v_new) hinv.card_le hvalid
    have hval' : Dynamic.ValuesBounded V (Function.update s_abs u (some v_new)) :=
      Dynamic.valuesBounded_step_of_valid (n_max := N) (o := .insert u v_new)
        hinv.val_bounded hvalid
    have htot_y1 : Succinct.totalSlots N (gmAtBit U w N y1.mem) =
        (Dynamic.dom (Function.update s_abs u (some v_new))).card := by
      rw [hgm_y1, hdict'.htot]
    exact ⟨hy_wf, hy_er, hinv.cap_le, hcard', hval', hinv.fit_cap,
      by rw [hy_sz, hy1_sz, htot_y1],
      hy_m0.trans htot_y1,
      (hy_ge1 1 (by omega)).trans ((hy1_low 1 h1_lt).trans hinv.hdr_cap),
      (hy_ge1 2 (by omega)).trans ((hy1_low 2 h2_lt).trans hinv.hdr_itemBits),
      (hy_ge1 3 (by omega)).trans ((hy1_low 3 h3_lt).trans hinv.hdr_metaBits),
      fun _ => ⟨hdict',
        fixedCoupled_of_ge_four_eq hw hy1_cpl hU.le hV.le (fun a ha => hy_ge1 a (by omega)),
        reducedKWise_rep_congr hhash (fun a ha_lo ha_hi =>
          (hy_ge1 a (by unfold offHash at ha_lo; omega)).trans (hy1_low a ha_hi))⟩⟩
  · unfold inEpochPotential
    rw [ite_eq_right hN0, ite_eq_right hN0]
    dsimp only [epochProbeExcess, s_fix', prog, h_q] at hT₁ ⊢
    omega

theorem inEpochDeleteOpRegCode_exec {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    (u : Fin U) (hr270 : x.regs 270 = u.val) :
    ∃ (s_fix' : Memory.State) (T : ℕ),
      BitRAM.DemonicExecWithin w inEpochDeleteOpRegCode x
        (fun y =>
          EpochDictInv U V w N θ (Function.update s_abs u none) s_fix' y) T ∧
      T + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + 292687 +
          350 * epochProbeExcess U N θ s_abs u := by
  have h4_ws : 4 ≤ x.wordSize w := four_le_wordSize_of_epochDictInv hw hinv
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  unfold inEpochDeleteOpRegCode
  by_cases hN0 : N = 0
  · subst hN0
    refine ⟨s_fix, 5, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := 4) hfit_1 ?_
      set s0 := x.set 12 1
      have hs0_adm : s0.regs 12 < s0.wordSize w := by
        change 1 < x.wordSize w; omega
      refine DemonicExecWithin.step_load (T := 3) hs0_adm ?_
      set s1 := s0.set 13 (s0.mem (s0.regs 12))
      refine DemonicExecWithin.step_const (T := 2) hfit_0 ?_
      set s2 := s1.set 12 0
      have hc : BitRAM.CondHolds (.eq 13 12) s2 := by
        change x.mem 1 = 0
        exact hinv.hdr_cap
      refine .branch_pos (T₀ := 1) hc ?_ (by omega)
      have hs2_wf : s2.WellFormed w :=
        wf_set 12 (wf_set 13 (wf_set 12 hinv.wf hfit_1)
          (by change Fits w (x.mem 1); rw [hinv.hdr_cap]; exact hfit_0)) hfit_0
      have hs2_er : EpochRegs U V w 0 s2 :=
        ((hinv.epoch_regs.set_of_outside (Or.inl (by decide)) 1).set_of_outside
          (Or.inl (by decide)) _).set_of_outside (Or.inl (by decide)) 0
      have hs_none : s_abs u = none := by
        by_contra hne
        have his : (s_abs u).isSome := Option.ne_none_iff_isSome.mp hne
        have hmem : u ∈ Dynamic.dom s_abs := Dictionary.mem_dom_iff_isSome.mpr his
        have hpos : 0 < (Dynamic.dom s_abs).card := Finset.card_pos.mpr ⟨u, hmem⟩
        have := hinv.card_le
        omega
      have hupd_eq : Function.update s_abs u none = s_abs := by
        funext k
        by_cases hk : k = u
        · subst hk; simp [hs_none]
        · simp [hk]
      refine nopRegCode_exec ?_
      rw [hupd_eq]
      exact ⟨hs2_wf, hs2_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
        hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
        hinv.active⟩
    · simp [inEpochPotential]; omega
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
    obtain ⟨hdict, hcpl, hhash⟩ := hinv.active hN_pos
    obtain ⟨hwf, henv, _⟩ :=
      dictEnv_of_fits_dictBitSize hw hN_pos hinv.cap_le hU hV.le hinv.fit_cap
    obtain ⟨found, j_del, phys_del, q_last, hspec⟩ :=
      Succinct.deleteWithHashProg_dict_spec hwf henv θ hdict u
    have hres_prep := hspec.1
    have hdict' := hspec.2.2.2.2.2.2.2.1
    clear hspec
    let h1 := Succinct.hValOfSeed U N θ
    let mOf := Succinct.mOfSeed U N θ
    let q := keyQuotient (bucketBits N) u.val
    let b := feistelBucket (bucketBits N) h1 u.val
    let m := mOf q
    let h_space := Succinct.hashSpace U w N
    have hb_eq :
        (h1 q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1)) = b :=
      and_mask_xor_eq_feistelBucket (bucketBits N) u.val (h1 q)
    have hq_eq : u.val >>> bucketBits N = q := Nat.shiftRight_eq_div_pow u.val (bucketBits N)
    have hprep_prog_eq :
        Succinct.deletePrepWithHashProg U V w N ((0, u.val), h1 q) =
          Succinct.deletePrepProg U V w N h_space (((0, b), q), m) := by
      change Succinct.deletePrepProg U V w N h_space
        (((0, (h1 q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
          u.val >>> bucketBits N), h1 q >>> bucketBits N) = _
      rw [hb_eq, hq_eq]; rfl
    let prep := (Memory.spec 0).clientResult s_fix
      (Succinct.deletePrepProg U V w N h_space (((0, b), q), m))
    have hprep_eq : prep = (((found, j_del), phys_del), q_last) := by
      dsimp only [prep]; rw [← hprep_prog_eq]; exact hres_prep
    let d_fin := (((((0, b), prep.1.1), prep.1.2), m), mOf prep.2)
    have hfin_prog_eq :
        Succinct.deleteFinishWithHashProg U V w N
          ((((0, u.val), h1 q), ((found, j_del), phys_del)), h1 q_last) =
          Succinct.deleteFinishProg U V w N h_space d_fin := by
      change Succinct.deleteFinishProg U V w N h_space
        (((((0, (h1 q &&& (2 ^ bucketBits N - 1)) ^^^ (u.val &&& (2 ^ bucketBits N - 1))),
          (found, j_del)), phys_del), h1 q >>> bucketBits N), h1 q_last >>> bucketBits N) = _
      rw [hb_eq]
      dsimp only [d_fin]
      rw [hprep_eq]
      rfl
    rw [hfin_prog_eq] at hdict'
    dsimp only [d_fin, prep, h_space, b, q, m, h1, mOf] at hdict'
    clear hres_prep hprep_prog_eq hprep_eq hfin_prog_eq
    let s0 := x.set 12 1
    let s1 := s0.set 13 (s0.mem (s0.regs 12))
    let s2 := s1.set 12 0
    have hs2_wf : s2.WellFormed w :=
      wf_set 12 (wf_set 13 (wf_set 12 hinv.wf hfit_1)
        (by change Fits w (x.mem 1); exact hinv.wf.mem_wf.mem_fits 1)) hfit_0
    have hs2_er : EpochRegs U V w N s2 :=
      ((hinv.epoch_regs.set_of_outside (Or.inl (by decide)) 1).set_of_outside
        (Or.inl (by decide)) _).set_of_outside (Or.inl (by decide)) 0
    have hs2_270 : s2.regs 270 = u.val := by
      simp +decide [s2, s1, s0, BitRAM.Data.set, hr270]
    have hgm_x : gmAtBit U w N x.mem = _ := hcpl.gm_eq
    have hs2_sz : s2.bitSize =
        dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N s2.mem)) := by
      change x.bitSize = dictBitSize U V w N (Succinct.totalSlots N (gmAtBit U w N x.mem))
      rw [hgm_x, hdict.htot, hinv.bitSize_eq]
    have hexec_del := inEpochDeleteRegCode_exec hwf henv hN_pos θ hdict u
      hs2_wf hs2_er hcpl hhash hinv.hdr_cap hinv.hdr_itemBits hinv.hdr_metaBits
      hs2_sz hinv.fit_cap hs2_270
    dsimp only at hexec_del
    obtain ⟨T₁, hExec₁, hT₁⟩ := hexec_del
    generalize (Memory.spec 0).clientState s_fix _ = s_fix' at hdict' hExec₁ hT₁
    have hdict'_s : Succinct.DictStateInv U V w N 0 θ (Function.update s_abs u none) s_fix' :=
      hdict'
    obtain ⟨L', hb_inv'⟩ := hdict'_s.hbucket
    refine ⟨s_fix', T₁ + 104, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := T₁ + 103) hfit_1 ?_
      have hs0_adm : s0.regs 12 < s0.wordSize w := by
        change 1 < x.wordSize w; omega
      refine DemonicExecWithin.step_load (T := T₁ + 102) hs0_adm ?_
      refine DemonicExecWithin.step_const (T := T₁ + 101) hfit_0 ?_
      have hc : ¬BitRAM.CondHolds (.eq 13 12) s2 := by
        change x.mem 1 ≠ 0
        rw [hinv.hdr_cap]
        exact hN0
      refine .branch_neg (T₀ := T₁ + 99) hc ?_ (by omega)
      refine .seq (T₁ := T₁) (T₂ := 99) hExec₁
        (fun y1 ⟨hy1_wf, hy1_er, hy1_sz, hy1_cpl, hy1_low⟩ => ?_) le_rfl
      have hgm_y1 : gmAtBit U w N y1.mem = _ := hy1_cpl.gm_eq
      have hslot_y1 : Succinct.SlotStoreInv N (gmAtBit U w N y1.mem) := by
        rw [hgm_y1]; exact hb_inv'.hslot
      have hsz_meta_y1 : epochMetaBits U w N ≤ y1.bitSize := by
        rw [hy1_sz]; exact Nat.le_add_right _ _
      refine (syncHdrCountRegCode_exec hw hN_pos hinv.cap_le hU hy1_wf hy1_er hslot_y1
        hsz_meta_y1).mono (fun y ⟨hy_wf, hy_er, hy_sz, hy_m0, hy_ge1⟩ => ?_) le_rfl
      have h1_lt : 1 < offLM U w N := by dsimp only [offLM, offHash]; omega
      have h2_lt : 2 < offLM U w N := by dsimp only [offLM, offHash]; omega
      have h3_lt : 3 < offLM U w N := by dsimp only [offLM, offHash]; omega
      have hcard' : (Dynamic.dom (Function.update s_abs u none)).card ≤ N :=
        (Dynamic.card_dom_delete_le s_abs u).trans hinv.card_le
      have hval' : Dynamic.ValuesBounded V (Function.update s_abs u none) :=
        Dynamic.valuesBounded_delete hinv.val_bounded u
      have htot_y1 : Succinct.totalSlots N (gmAtBit U w N y1.mem) =
          (Dynamic.dom (Function.update s_abs u none)).card := by
        rw [hgm_y1, hdict'_s.htot]
      have hy_low : ∀ a < offLM U w N, y1.mem a = x.mem a := hy1_low
      have hy_hdr1 : y.mem 1 = N :=
        (hy_ge1 1 (by omega)).trans ((hy_low 1 h1_lt).trans hinv.hdr_cap)
      have hy_hdr2 : y.mem 2 = itemBits U V N :=
        (hy_ge1 2 (by omega)).trans ((hy_low 2 h2_lt).trans hinv.hdr_itemBits)
      have hy_hdr3 : y.mem 3 = epochMetaBits U w N :=
        (hy_ge1 3 (by omega)).trans ((hy_low 3 h3_lt).trans hinv.hdr_metaBits)
      have hy_cpl : FixedCoupled U V w N s_fix' y.toBitMemoryState :=
        fixedCoupled_of_ge_four_eq hw hy1_cpl hU.le hV.le (fun a ha => hy_ge1 a (by omega))
      have hy_hash : ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
          (totalMicroBits N) 3 θ y.mem :=
        reducedKWise_rep_congr hhash (fun a ha_lo ha_hi =>
          (hy_ge1 a (by dsimp only [offHash] at ha_lo; omega)).trans (hy_low a ha_hi))
      exact ⟨hy_wf, hy_er, hinv.cap_le, hcard', hval', hinv.fit_cap,
        by rw [hy_sz, hy1_sz, htot_y1],
        hy_m0.trans htot_y1, hy_hdr1, hy_hdr2, hy_hdr3,
        fun _ => ⟨hdict'_s, hy_cpl, hy_hash⟩⟩
    · unfold inEpochPotential
      rw [ite_eq_right hN0, ite_eq_right hN0]
      dsimp only [epochProbeExcess]
      omega


/-! ## Section 5: Unified `inEpochStepRegCode` execution, expectation bound, and empty witness -/

/-- **Unified in-epoch machine step (`inEpochStepRegCode_exec`):**
the single fixed parameter-free program `inEpochStepRegCode : BitRAM.Code .standard 280` executes
any admissible in-epoch `query`, `insert`, or `delete` from `loadOpRegs op x` under demonic `.grow`,
preserving `EpochDictInv`, establishing `OpOutputCorrect`, and running in at most
`inEpochStepOverhead U N θ s_abs op` amortized instructions against `1967 * inEpochPotential`. -/
theorem inEpochStepRegCode_exec {U V w N : ℕ} (hw : 0 < w)
    (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    {op : Dynamic.Op U} (hvalid : (Dynamic.spec U V N).valid s_abs op) :
    ∃ (s_fix' : Memory.State) (T : ℕ),
      BitRAM.DemonicExecWithin w inEpochStepRegCode (loadOpRegs op x)
        (fun y =>
          EpochDictInv U V w N θ ((Dynamic.spec U V N).stepFn s_abs op).1 s_fix' y ∧
          OpOutputCorrect s_abs op y.regs) T ∧
      T + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + inEpochStepOverhead U N θ s_abs op := by
  have hinv_in : EpochDictInv U V w N θ s_abs s_fix (loadOpRegs op x) :=
    loadOpRegs_preserves_inv hw hU hV hinv hvalid
  have hfit_0 : Fits w 0 := fits_zero w
  have hfit_1 : Fits w 1 := fits_one (Nat.ne_of_gt hw)
  unfold inEpochStepRegCode
  cases op with
  | query u =>
    set x0 := loadOpRegs (.query u) x
    set s0 := x0.set 12 0
    have hs0_wf : s0.WellFormed w := wf_set 12 hinv_in.wf hfit_0
    have hs0_er : EpochRegs U V w N s0 :=
      hinv_in.epoch_regs.set_of_outside (Or.inl (by decide)) 0
    have hs0_inv : EpochDictInv U V w N θ s_abs s_fix s0 :=
      ⟨hs0_wf, hs0_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
        hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
        hinv.active⟩
    have hs0_270 : s0.regs 270 = u.val := by
      simp +decide [s0, x0, loadOpRegs, BitRAM.Data.set]
    obtain ⟨T_q, hExec_q, hT_q⟩ := queryOpRegCode_exec hw hU hV θ hs0_inv u hs0_270
    refine ⟨s_fix, T_q + 2, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := T_q + 1) hfit_0 ?_
      have hc : BitRAM.CondHolds (.eq 278 12) s0 := by
        change s0.regs 278 = s0.regs 12
        simp +decide [s0, x0, loadOpRegs, BitRAM.Data.set]
      refine .branch_pos (T₀ := T_q) hc ?_ (by omega)
      exact hExec_q.mono (fun y ⟨hy_inv, hy_out⟩ => ⟨hy_inv, hy_out⟩) le_rfl
    · dsimp only [inEpochStepOverhead, opKey]
      omega
  | insert u v =>
    set x0 := loadOpRegs (.insert u v) x
    set s0 := x0.set 12 0
    set s1 := s0.set 12 1
    have hs1_wf : s1.WellFormed w := wf_set 12 (wf_set 12 hinv_in.wf hfit_0) hfit_1
    have hs1_er : EpochRegs U V w N s1 :=
      (hinv_in.epoch_regs.set_of_outside (Or.inl (by decide)) 0).set_of_outside
        (Or.inl (by decide)) 1
    have hs1_inv : EpochDictInv U V w N θ s_abs s_fix s1 :=
      ⟨hs1_wf, hs1_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
        hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
        hinv.active⟩
    have hs1_270 : s1.regs 270 = u.val := by
      simp +decide [s1, s0, x0, loadOpRegs, BitRAM.Data.set]
    have hs1_274 : s1.regs 274 = v := by
      simp +decide [s1, s0, x0, loadOpRegs, BitRAM.Data.set]
    obtain ⟨s_fix', T_i, hExec_i, hT_i⟩ :=
      inEpochInsertOpRegCode_exec hw hU hV θ hs1_inv u v hvalid hs1_270 hs1_274
    refine ⟨s_fix', T_i + 5, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := T_i + 4) hfit_0 ?_
      have hc0 : ¬BitRAM.CondHolds (.eq 278 12) s0 := by
        change s0.regs 278 ≠ s0.regs 12
        simp +decide [s0, x0, loadOpRegs, BitRAM.Data.set]
      refine .branch_neg (T₀ := T_i + 2) hc0 ?_ (by omega)
      refine DemonicExecWithin.step_const (T := T_i + 1) hfit_1 ?_
      have hc1 : BitRAM.CondHolds (.eq 278 12) s1 := by
        change s1.regs 278 = s1.regs 12
        simp +decide [s1, s0, x0, loadOpRegs, BitRAM.Data.set]
      refine .branch_pos (T₀ := T_i) hc1 ?_ (by omega)
      exact hExec_i.mono (fun y hy_inv => ⟨hy_inv, trivial⟩) le_rfl
    · dsimp only [inEpochStepOverhead, opKey]
      omega
  | delete u =>
    set x0 := loadOpRegs (.delete u) x
    set s0 := x0.set 12 0
    set s1 := s0.set 12 1
    have hs1_wf : s1.WellFormed w := wf_set 12 (wf_set 12 hinv_in.wf hfit_0) hfit_1
    have hs1_er : EpochRegs U V w N s1 :=
      (hinv_in.epoch_regs.set_of_outside (Or.inl (by decide)) 0).set_of_outside
        (Or.inl (by decide)) 1
    have hs1_inv : EpochDictInv U V w N θ s_abs s_fix s1 :=
      ⟨hs1_wf, hs1_er, hinv.cap_le, hinv.card_le, hinv.val_bounded, hinv.fit_cap,
        hinv.bitSize_eq, hinv.hdr_count, hinv.hdr_cap, hinv.hdr_itemBits, hinv.hdr_metaBits,
        hinv.active⟩
    have hs1_270 : s1.regs 270 = u.val := by
      simp +decide [s1, s0, x0, loadOpRegs, BitRAM.Data.set]
    obtain ⟨s_fix', T_d, hExec_d, hT_d⟩ :=
      inEpochDeleteOpRegCode_exec hw hU hV θ hs1_inv u hs1_270
    refine ⟨s_fix', T_d + 6, ?_, ?_⟩
    · refine DemonicExecWithin.step_const (T := T_d + 5) hfit_0 ?_
      have hc0 : ¬BitRAM.CondHolds (.eq 278 12) s0 := by
        change s0.regs 278 ≠ s0.regs 12
        simp +decide [s0, x0, loadOpRegs, BitRAM.Data.set]
      refine .branch_neg (T₀ := T_d + 3) hc0 ?_ (by omega)
      refine DemonicExecWithin.step_const (T := T_d + 2) hfit_1 ?_
      have hc1 : ¬BitRAM.CondHolds (.eq 278 12) s1 := by
        change s1.regs 278 ≠ s1.regs 12
        simp +decide [s1, s0, x0, loadOpRegs, BitRAM.Data.set]
      refine .branch_neg (T₀ := T_d) hc1 ?_ (by omega)
      exact hExec_d.mono (fun y hy_inv => ⟨hy_inv, trivial⟩) le_rfl
    · dsimp only [inEpochStepOverhead, opKey]
      omega

/-- Deterministic fuel-evaluator corollary of `inEpochStepRegCode_exec` under any concrete
`DirtyGrowOracle w oracle`. -/
theorem inEpochStepRegCode_evalWithOracle {U V w N : ℕ}
    {oracle : (ℕ → ℕ) → ℕ → ℕ → (ℕ → ℕ)} (horacle : DirtyGrowOracle w oracle)
    (hw : 0 < w) (hU : Fits w U) (hV : Fits w V)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {s_fix : Memory.State}
    {x : BitRAM.Data 280} (hinv : EpochDictInv U V w N θ s_abs s_fix x)
    {op : Dynamic.Op U} (hvalid : (Dynamic.spec U V N).valid s_abs op) :
    ∃ (s_fix' : Memory.State) (T : ℕ),
      let y := evalWithOracle w oracle T inEpochStepRegCode (loadOpRegs op x)
      EpochDictInv U V w N θ ((Dynamic.spec U V N).stepFn s_abs op).1 s_fix' y ∧
      OpOutputCorrect s_abs op y.regs ∧
      ExecCodeDistWithOracle w oracle inEpochStepRegCode (loadOpRegs op x)
        (PMF.pure y) (T : ℝ≥0∞) ∧
      (∀ fuel ≥ T, evalWithOracle w oracle fuel inEpochStepRegCode (loadOpRegs op x) = y) ∧
      T + 1967 * inEpochPotential U V w N s_fix' ≤
        1967 * inEpochPotential U V w N s_fix + inEpochStepOverhead U N θ s_abs op := by
  obtain ⟨s_fix', T, hExec, hT⟩ := inEpochStepRegCode_exec hw hU hV θ hinv hvalid
  obtain ⟨⟨hinv', hout'⟩, hdist, hfuel⟩ := hExec.evalWithOracle_spec_of_le horacle
  exact ⟨s_fix', T, hinv', hout', hdist, hfuel, hT⟩

/-- **Expected `O(1)` amortized instruction overhead (`tsum_inEpochStepOverhead_le`):**
for any state `s_abs` with `#(Dynamic.dom s_abs) ≤ N ≤ U` and any operation `op`, the uniform
expectation of `inEpochStepOverhead U N θ s_abs op` over `θ : Succinct.QuotHashSeed U N` is at
most `294450` (`= 292700 + 5 * 350`). -/
theorem tsum_inEpochStepOverhead_le {U N : ℕ} (hnU : N ≤ U)
    (s_abs : Dynamic.State U) (hcard : (Dynamic.dom s_abs).card ≤ N) (op : Dynamic.Op U) :
    (∑' θ : Succinct.QuotHashSeed U N,
      (PMF.uniformOfFintype (Succinct.QuotHashSeed U N)) θ *
        (inEpochStepOverhead U N θ s_abs op : ℝ≥0∞)) ≤ 294450 := by
  have herase : #((Dynamic.dom s_abs).erase (opKey op)) ≤ N :=
    Finset.card_erase_le.trans hcard
  simpa using Succinct.tsum_affine_probeExcess_reducedPolyHash_le hnU
    (Dynamic.dom s_abs) (opKey op) herase 292700 350
    (fun θ => inEpochStepOverhead U N θ s_abs op)
    (fun _ => le_rfl)

/-- **Non-vacuity and active-epoch empty initialization witness (`exists_empty_epochDictInv`):**
for every `0 < w`, `N ≤ U`, `Fits w U`, `Fits w V`, `Fits w (dictBitSize U V w N N)`, and seed
`θ : Succinct.QuotHashSeed U N`, there exist `s_fix` and `x : BitRAM.Data 280` satisfying
`EpochDictInv U V w N θ (Dynamic.empty U) s_fix x` with `inEpochPotential U V w N s_fix = 0`. -/
theorem exists_empty_epochDictInv {U V w N : ℕ} (hw : 0 < w)
    (hNU : N ≤ U) (hU : Fits w U) (hV : Fits w V)
    (hfit_cap : Fits w (dictBitSize U V w N N))
    (θ : Succinct.QuotHashSeed U N) :
    ∃ (s_fix : Memory.State) (x : BitRAM.Data 280),
      EpochDictInv U V w N θ (Dynamic.empty U) s_fix x ∧
      inEpochPotential U V w N s_fix = 0 := by
  have hfit_0 : Fits w 0 := fits_zero w
  have hw_lt : w < 2 ^ w := Nat.lt_two_pow_self
  by_cases hN0 : N = 0
  · subst hN0
    let x_init : BitRAM.Data 280 :=
      ⟨fun r => if r.val = 240 then U else if r.val = 241 then V else 0,
        BitMemory.empty.mem, BitMemory.empty.bitSize⟩
    have hx_wf : x_init.WellFormed w := {
      regs_fits r := by
        dsimp only [x_init]
        split_ifs
        · exact hU
        · exact hV
        · exact hfit_0
      mem_wf := BitMemory.wellFormed_empty w
    }
    have hfit_4w : Fits w (4 * w) := by
      simpa [dictBitSize, epochMetaBits, epochMetaWords] using hfit_cap
    have hexec := initEmptyRegCode_exec hw hU hV hfit_4w θ hx_wf rfl
      (by simp +decide [x_init]) (by simp +decide [x_init])
    obtain ⟨⟨hinv, _, _⟩, _, _⟩ :=
      hexec.evalWithOracle_spec_of_le (dirtyGrowOracle_zeroGrowOracle hw)
    exact ⟨⟨fun _ => 0, 0⟩, _, hinv, rfl⟩
  · have hN_pos : 0 < N := Nat.pos_of_ne_zero hN0
    let w₀ := Succinct.qBits U N
    let b := Succinct.hashB N
    let b' := totalMicroBits N
    let t := epochTrinomialStep U N
    let c := reducedChunkBits t
    let p := reducedPackShift t w
    let L := reducedLimbCount t
    obtain ⟨_, _, hfit_hash⟩ := dictEnv_of_fits_dictBitSize hw hN_pos hNU hU hV.le hfit_cap
    have hw2 : 2 ≤ w := by
      have h8 : 8 ≤ Succinct.hashSpace U w N := Succinct.eight_le_hashSpace U w N
      have hlt : 8 < 2 ^ w := lt_of_le_of_lt (by omega) hfit_hash
      by_contra h
      have hw1 : w ≤ 1 := by omega
      have hpow : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right two_pos hw1
      omega
    have hc_le : 2 * c ≤ w := Succinct.two_mul_reducedChunkBits_hash_le hw2 hNU hU.le
    have hc_lt : 2 * c < w :=
      ReducedKWise.two_mul_reducedChunkBits_lt_of_fits_space hc_le hfit_hash
    have hL_pos : 0 < L := reducedLimbCount_pos t
    let x_w : Cslib.WordRAM.Data 240 := ⟨fun _ => offHash, fun _ => 0⟩
    obtain ⟨y_tab, _, _, htab, htab_out⟩ :=
      ReducedKWise.initTableCode_exec (w := w) (base := offHash) (w₀ := w₀) (b := b) (b' := b')
        (k := 3) (x := x_w) rfl hc_le hfit_hash
    let mem_x : ℕ → ℕ := fun a =>
      if a = 0 then 0
      else if a = 1 then N
      else if a = 2 then itemBits U V N
      else if a = 3 then epochMetaBits U w N
      else if a = offHash then θ.1.val
      else if h : offHash + 1 ≤ a ∧ a < offHash + 1 + 3 * L then
        getLimb c (θ.2 ⟨(a - (offHash + 1)) / L,
          (Nat.div_lt_iff_lt_mul hL_pos).mpr (by rw [Nat.mul_comm]; omega)⟩).val
          ((a - (offHash + 1)) % L)
      else y_tab.mem a
    have hmeta_le_cap : epochMetaBits U w N ≤ dictBitSize U V w N N := Nat.le_add_right _ _
    have hfit_meta_bits : Fits w (epochMetaBits U w N) := hfit_cap.of_le hmeta_le_cap
    have hfit_meta_words : Fits w (epochMetaWords U w N) :=
      hfit_meta_bits.of_le (Nat.le_mul_of_pos_right _ hw)
    have hqw_le : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU.le
    have hvw_le : valBits V ≤ w := valBits_le_of_le_pow hV.le
    have hmem_ge_lm : ∀ a, offLM U w N ≤ a → mem_x a = 0 := by
      intro a ha
      have ha4 : 4 < a := by
        have h8 := Succinct.eight_le_hashSpace U w N
        unfold offLM offHash at ha
        omega
      have ha_seed : offHash + 1 + 3 * L ≤ a := by
        have hspace : Succinct.hashSpace U w N = ReducedKWise.space w w₀ b b' 3 := rfl
        unfold offLM at ha; rw [hspace] at ha
        unfold ReducedKWise.space ReducedKWise.seedWords at ha
        change offHash + (1 + 3 * L + ReducedKWise.tableWords w w₀ b b') ≤ a at ha
        omega
      dsimp only [mem_x]
      have h0 : a ≠ 0 := by omega
      have h1 : a ≠ 1 := by omega
      have h2 : a ≠ 2 := by omega
      have h3 : a ≠ 3 := by omega
      have h4 : a ≠ offHash := by unfold offHash; omega
      have h5 : ¬(offHash + 1 ≤ a ∧ a < offHash + 1 + 3 * L) := by omega
      rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
        ite_eq_right h4, dite_eq_right h5]
      exact htab_out a (Or.inr ha)
    have hmem_fits : ∀ q, Fits w (mem_x q) := by
      intro q
      dsimp only [mem_x]
      split_ifs with h0 h1 h2 h3 h4 h5
      · exact hfit_0
      · exact fits_of_le_N hw hNU hU (Nat.le_max_left N 1)
      · have hle : itemBits U V N ≤ 2 * w := itemBits_le_two_mul_w hU.le hV.le
        have h4w : 4 * w < 2 ^ w := hfit_meta_bits.of_le (by
          have : 4 ≤ epochMetaWords U w N := by unfold epochMetaWords; rw [ite_eq_right hN0]; omega
          exact Nat.mul_le_mul_right w this)
        exact Fits.of_le h4w (by omega)
      · exact hfit_meta_bits
      · have hw0_le : w₀ ≤ w := Succinct.qBits_le_of_le_pow hw hU.le
        exact lt_of_lt_of_le θ.1.isLt (Nat.pow_le_pow_right two_pos (by omega))
      · have hlimb : getLimb c
            (θ.2 ⟨(q - (offHash + 1)) / L,
              (Nat.div_lt_iff_lt_mul hL_pos).mpr (by rw [Nat.mul_comm]; omega)⟩).val
            ((q - (offHash + 1)) % L) < 2 ^ c :=
          getLimb_lt c _ _
        exact lt_of_lt_of_le hlimb (Nat.pow_le_pow_right two_pos (by omega))
      · by_cases htab_in : ReducedKWise.tabBase offHash w₀ b b' 3 ≤ q ∧
            q < offHash + ReducedKWise.space w w₀ b b' 3
        · have hwIdx : q - ReducedKWise.tabBase offHash w₀ b b' 3 <
              ReducedKWise.tableWords w w₀ b b' := by
            dsimp only [ReducedKWise.tabBase, ReducedKWise.space] at htab_in ⊢
            omega
          have hlt_pack := htab.1 (q - ReducedKWise.tabBase offHash w₀ b b' 3) hwIdx
          rw [Nat.add_sub_of_le htab_in.1] at hlt_pack
          have hpack_le : 2 ^ p * (2 * c) ≤ w := two_pow_reducedPackShift_mul_le hc_le
          exact lt_of_lt_of_le hlt_pack (Nat.pow_le_pow_right two_pos hpack_le)
        · rw [htab_out q (by omega)]
          exact hfit_0
    let regs_x : Fin 280 → ℕ := fun r =>
      match r.val with
      | 240 => U
      | 241 => V
      | 242 => keyBits U
      | 243 => valBits V
      | 244 => quotientBits U N
      | 245 => bucketBits N
      | 246 => numBuckets N
      | 247 => numBuckets N - 1
      | 248 => numMicroPerBucket N
      | 249 => b'
      | 250 => slabSize N
      | 251 => effBucketCap N
      | 252 => effBucketPosBits N
      | 253 => maxTailItems N
      | 254 => globalPtrBits N
      | 255 => Succinct.lmSubWords N w
      | 256 => offLM U w N
      | 257 => offGM U w N
      | 258 => offTD U w N
      | 259 => offDT U w N
      | 260 => epochMetaWords U w N
      | 261 => w₀
      | 262 => w₀ - min w₀ (3 * b)
      | 263 => min t 3
      | 264 => c
      | 265 => 2 ^ c - 1
      | 266 => p
      | 267 => 2 ^ p - 1
      | 268 => 2 ^ (2 * c) - 1
      | 269 => ReducedKWise.tabBase offHash w₀ b b' 3
      | _ => 0
    let x_out : BitRAM.Data 280 := ⟨regs_x, mem_x, epochMetaBits U w N⟩
    have hx_mem_wf : x_out.toBitMemoryState.WellFormed w := {
      mem_fits := hmem_fits
      bitSize_fits := hfit_meta_bits
      zero_above i hi := by
        change (mem_x (0 + i / w)).testBit (i % w) = false
        rw [Nat.zero_add]
        have hge_meta : epochMetaWords U w N ≤ i / w := (Nat.le_div_iff_mul_le hw).mpr hi
        have hge_lm : offLM U w N ≤ i / w := by
          have : offLM U w N ≤ epochMetaWords U w N := by
            rw [← offDT_add_eq_epochMetaWords hN_pos]
            unfold offDT offTD offGM; omega
          omega
        rw [hmem_ge_lm (i / w) hge_lm]
        exact Nat.zero_testBit _
    }
    have hfit_N : ∀ v ≤ max N 1, Fits w v := fun v hv => fits_of_le_N hw hNU hU hv
    have hb'_le : b' ≤ w := totalMicroBits_le_of_le_pow hNU hU.le
    have hw0_le : w₀ ≤ w := Succinct.qBits_le_of_le_pow hw hU.le
    have hp_le : p ≤ 2 * c := reducedPackShift_le t w
    have hpow2c_lt : 2 ^ (2 * c) < 2 ^ w := Nat.pow_lt_pow_right one_lt_two hc_lt
    have hcap_eff_le : effBucketCap N ≤ epochMetaBits U w N := by
      have hpos_bits : 1 ≤ effBucketPosBits N := by
        unfold effBucketPosBits
        have hmin_pos : 1 ≤ min N (effBucketCap N) := by
          unfold effBucketCap numMicroPerBucket
          have := Nat.one_le_two_pow (n := microBits N)
          omega
        calc 1 = Nat.clog 2 2 := by decide
          _ ≤ Nat.clog 2 (min N (effBucketCap N) + 1) := Nat.clog_mono_right 2 (by omega)
      have hm_le_tot : numMicroPerBucket N ≤ totalMicroBuckets N := by
        rw [totalMicroBuckets_eq_mul]
        exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
      have hmul1 : totalMicroBuckets N ≤ totalMicroBuckets N * effBucketPosBits N :=
        Nat.le_mul_of_pos_right _ hpos_bits
      have hmul2 : totalMicroBuckets N * effBucketPosBits N ≤ Succinct.lmSubWords N w * w :=
        mul_le_packedWords_mul _ _ w hw
      have h9 : 9 * Succinct.lmSubWords N w ≤ epochMetaWords U w N := by
        unfold epochMetaWords; rw [ite_eq_right hN0]; omega
      have h9w : 9 * (Succinct.lmSubWords N w * w) ≤ epochMetaBits U w N := by
        unfold epochMetaBits
        calc 9 * (Succinct.lmSubWords N w * w) = (9 * Succinct.lmSubWords N w) * w := by ring
          _ ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w h9
      unfold effBucketCap
      omega
    have hU_lt : U < 2 ^ w := hU
    have hnb_le : numBuckets N ≤ totalMicroBuckets N := by
      rw [totalMicroBuckets_eq_mul]
      exact Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    have hm_le_tot : numMicroPerBucket N ≤ totalMicroBuckets N := by
      rw [totalMicroBuckets_eq_mul]
      exact Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have hx_wf : x_out.WellFormed w := {
      regs_fits r := by
        dsimp only [x_out, regs_x]
        split
        · exact hU
        · exact hV
        · exact lt_of_le_of_lt (Nat.clog_le_of_le_pow hU.le) hw_lt
        · exact lt_of_le_of_lt hvw_le hw_lt
        · exact lt_of_le_of_lt hqw_le hw_lt
        · exact lt_of_le_of_lt ((bucketBits_le_totalMicroBits N).trans hb'_le) hw_lt
        · exact hfit_N _ (hnb_le.trans (totalMicroBuckets_le N))
        · exact hfit_N _ ((Nat.sub_le _ _).trans (hnb_le.trans (totalMicroBuckets_le N)))
        · exact hfit_N _ (hm_le_tot.trans (totalMicroBuckets_le N))
        · exact lt_of_le_of_lt hb'_le hw_lt
        · exact hfit_N _ (Succinct.slabSize_le_max_n_one N)
        · exact hfit_meta_bits.of_le hcap_eff_le
        · have hle_N1 : min N (effBucketCap N) + 1 ≤ 2 ^ w := by
            have := Nat.min_le_left N (effBucketCap N); omega
          exact lt_of_le_of_lt (Nat.clog_le_of_le_pow hle_N1) hw_lt
        · exact hfit_N _ ((maxTailItems_le N).trans (Nat.le_max_left N 1))
        · have hN1 : N + 1 ≤ 2 ^ w := by omega
          exact lt_of_le_of_lt (Nat.clog_le_of_le_pow hN1) hw_lt
        · exact hfit_meta_words.of_le (by
            unfold epochMetaWords; rw [ite_eq_right hN0]; omega)
        · exact hfit_meta_words.of_le (by
            rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD offGM; omega)
        · exact hfit_meta_words.of_le (by
            rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)
        · exact hfit_meta_words.of_le (by
            rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)
        · exact hfit_meta_words.of_le (by
            rw [← offDT_add_eq_epochMetaWords hN_pos]; omega)
        · exact hfit_meta_words
        · exact lt_of_le_of_lt hw0_le hw_lt
        · exact lt_of_le_of_lt ((Nat.sub_le _ _).trans hw0_le) hw_lt
        · have h4w : 4 ≤ epochMetaWords U w N := by
            unfold epochMetaWords; rw [ite_eq_right hN0]; omega
          exact hfit_meta_words.of_le ((Nat.min_le_right t 3).trans (by omega))
        · exact lt_of_le_of_lt (by omega : c ≤ w) hw_lt
        · exact lt_of_le_of_lt ((Nat.sub_le _ _).trans
            (Nat.pow_le_pow_right two_pos (by omega : c ≤ 2 * c))) hpow2c_lt
        · exact lt_of_le_of_lt (hp_le.trans hc_le) hw_lt
        · exact lt_of_le_of_lt ((Nat.sub_le _ _).trans
            (Nat.pow_le_pow_right two_pos hp_le)) hpow2c_lt
        · exact lt_of_le_of_lt (Nat.sub_le _ _) hpow2c_lt
        · exact hfit_hash.of_le (by
            change offHash + ReducedKWise.seedWords w₀ b b' 3 ≤
              offHash + ReducedKWise.space w w₀ b b' 3
            unfold ReducedKWise.space; omega)
        · exact hfit_0
      mem_wf := hx_mem_wf
    }
    have hx_er : EpochRegs U V w N x_out := {
      r240 := rfl
      r241 := rfl
      r242 := rfl
      r243 := rfl
      r244 := rfl
      active _ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    }
    let s_fix : Memory.State := ⟨fun _ => 0, Succinct.space U V w N⟩
    have hgm_fix0 : ∀ i, Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem i = 0 := by
      intro i
      unfold Succinct.gmAt
      split_ifs
      · exact readPacked_zero rfl rfl
      · rfl
    have hlm_fix0 : ∀ q, Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem q = 0 := by
      rintro ⟨col, j⟩
      unfold Succinct.lmAt
      split_ifs
      · exact readPacked_zero rfl rfl
      · rfl
    obtain ⟨hdict, hpot0⟩ := Succinct.dictStateInv_of_zero θ (s := s_fix) hgm_fix0 hlm_fix0
    have hgm_bit0 : ∀ i, gmAtBit U w N x_out.mem i = 0 := by
      intro i
      unfold gmAtBit
      split_ifs with hi
      · dsimp only [x_out]
        apply readPacked_zero
        · apply hmem_ge_lm; dsimp only [offGM]; omega
        · apply hmem_ge_lm; dsimp only [offGM]; omega
      · rfl
    have hlm_bit0 : ∀ q, lmAtBit U w N x_out.mem q = 0 := by
      rintro ⟨col, j⟩
      unfold lmAtBit
      split_ifs with hcj
      · dsimp only [x_out]
        apply readPacked_zero
        · apply hmem_ge_lm; dsimp only [offLMSub]; omega
        · apply hmem_ge_lm; dsimp only [offLMSub]; omega
      · rfl
    have htd_bit0 : ∀ i, tdAtBit U w N x_out.mem i = 0 := by
      intro i
      unfold tdAtBit
      split_ifs with hi
      · dsimp only [x_out]
        apply readPacked_zero
        · apply hmem_ge_lm; dsimp only [offTD, offGM]; omega
        · apply hmem_ge_lm; dsimp only [offTD, offGM]; omega
      · rfl
    have hdt_bit0 : ∀ i, dtAtBit U w N x_out.mem i = 0 := by
      intro i
      unfold dtAtBit
      split_ifs with hi
      · dsimp only [x_out]
        apply readPacked_zero
        · apply hmem_ge_lm; dsimp only [offDT, offTD, offGM]; omega
        · apply hmem_ge_lm; dsimp only [offDT, offTD, offGM]; omega
      · rfl
    have htot_bit0 : Succinct.totalSlots N (gmAtBit U w N x_out.mem) = 0 := by
      unfold Succinct.totalSlots
      split_ifs <;> simp [hgm_bit0]
    have hcpl : FixedCoupled U V w N s_fix x_out.toBitMemoryState := {
      gm_eq := funext fun i => (hgm_bit0 i).trans (hgm_fix0 i).symm
      lm_eq := funext fun q => (hlm_bit0 q).trans (hlm_fix0 q).symm
      win_inv := by
        dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hgm_bit0 1]
        exact ⟨fun _ h => by omega, fun _ h => by omega,
          fun _ h => by omega, fun _ _ _ => by omega⟩
      td_lt i := by
        dsimp only [BitRAM.Data.toBitMemoryState]
        rw [htd_bit0 i]
        omega
      dt_lt i := by
        dsimp only [BitRAM.Data.toBitMemoryState]
        rw [hdt_bit0 i]
        omega
      quot_eq d hd := by
        dsimp only [BitRAM.Data.toBitMemoryState] at hd
        rw [htot_bit0] at hd; omega
      val_eq d hd := by
        dsimp only [BitRAM.Data.toBitMemoryState] at hd
        rw [htot_bit0] at hd; omega
    }
    have hhash : ReducedKWise.Rep offHash w w₀ b b' 3 θ x_out.mem := by
      have hmem_tab_eq : ∀ a, ReducedKWise.tabBase offHash w₀ b b' 3 ≤ a →
          x_out.mem a = y_tab.mem a := by
        intro a ha
        dsimp only [x_out, mem_x]
        unfold ReducedKWise.tabBase ReducedKWise.seedWords at ha
        change offHash + (1 + 3 * L) ≤ a at ha
        have h0 : a ≠ 0 := by unfold offHash at ha; omega
        have h1 : a ≠ 1 := by unfold offHash at ha; omega
        have h2 : a ≠ 2 := by unfold offHash at ha; omega
        have h3 : a ≠ 3 := by unfold offHash at ha; omega
        have h4 : a ≠ offHash := by omega
        have h5 : ¬(offHash + 1 ≤ a ∧ a < offHash + 1 + 3 * L) := by omega
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
          ite_eq_right h4, dite_eq_right h5]
      refine ⟨⟨fun wIdx hwIdx => ?_, fun idx hidx => ?_⟩, ?_, fun j m => ?_⟩
      · rw [hmem_tab_eq _ (Nat.le_add_right _ _)]
        exact htab.1 wIdx hwIdx
      · rw [hmem_tab_eq _ (Nat.le_add_right _ _)]
        exact htab.2 idx hidx
      · simp +decide [x_out, mem_x, offHash]
      · have hm_lt : m.val < L := m.isLt
        have hlt_seed : m.val + L * j.val < 3 * L := by
          have hj : j.val + 1 ≤ 3 := j.isLt
          have hmul : L * (j.val + 1) ≤ L * 3 := Nat.mul_le_mul_left L hj
          rw [Nat.mul_add, Nat.mul_one] at hmul
          omega
        let idx := m.val + L * j.val
        let a := offHash + 1 + idx
        have h0 : a ≠ 0 := by dsimp only [a, offHash]; omega
        have h1 : a ≠ 1 := by dsimp only [a, offHash]; omega
        have h2 : a ≠ 2 := by dsimp only [a, offHash]; omega
        have h3 : a ≠ 3 := by dsimp only [a, offHash]; omega
        have h4 : a ≠ offHash := by dsimp only [a, offHash]; omega
        have h5 : offHash + 1 ≤ a ∧ a < offHash + 1 + 3 * L := by dsimp only [a]; omega
        change mem_x a = getLimb c (θ.2 j).val m.val
        dsimp only [mem_x]
        rw [ite_eq_right h0, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
          ite_eq_right h4, dite_eq_left h5]
        have hsub : a - (offHash + 1) = idx := by dsimp only [a]; omega
        have hdiv : idx / L = j.val := by
          dsimp only [idx]
          rw [Nat.add_mul_div_left _ _ hL_pos, Nat.div_eq_of_lt hm_lt, Nat.zero_add]
        have hmod : idx % L = m.val := by
          dsimp only [idx]
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hm_lt]
        have hfin_eq : (⟨(a - (offHash + 1)) / L,
            (Nat.div_lt_iff_lt_mul hL_pos).mpr (by rw [Nat.mul_comm]; omega)⟩ : Fin 3) = j := by
          ext; simp [hsub, hdiv]
        rw [hfin_eq, hsub, hmod]
    refine ⟨s_fix, x_out, ⟨hx_wf, hx_er, hNU, by simp,
      fun _ _ h => by simp [Dynamic.empty, Dictionary.empty] at h,
      hfit_cap, by simp [x_out, dictBitSize], by simp +decide [x_out, mem_x],
      by simp +decide [x_out, mem_x], by simp +decide [x_out, mem_x],
      by simp +decide [x_out, mem_x], fun _ => ⟨hdict, hcpl, hhash⟩⟩, ?_⟩
    unfold inEpochPotential
    rw [ite_eq_right hN0]
    exact hpot0

end Cslib.DataStructure.Dictionary.BitResizable
