/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Query

/-!
# Concrete `BitRAM` State-Synchronization Programs under Demonic `.grow`

This module builds on `Complexity.DataStructure.Dictionary.BitResizable.Query` to provide concrete
`BitRAM.Code .standard 12` state-synchronization programs under demonic `.grow`
(`inEpochInsertSyncCode`, `inEpochDeleteSyncCode`, `rebuildSyncCode`) that transition the
bit-resizable memory state to any target state `s_tar` satisfying `Rep`.
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

/-! ## Section 1: Bit-level preservation and single-item grow/shrink primitives -/

/-- If two well-formed `BitMemory.State`s agree on all bits `< dictBitSize U V w N m`, they agree on
all metadata words `< epochMetaWords U w N` and all dense items `< m`. -/
theorem preserve_meta_and_items_of_getBit_eq {U V w N m : ℕ}
    {s₁ s₂ : BitMemory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hs₁ : s₁.WellFormed w) (hs₂ : s₂.WellFormed w)
    (hbit : ∀ i < dictBitSize U V w N m, s₁.getBit w i = s₂.getBit w i) :
    (∀ a < epochMetaWords U w N, s₁.mem a = s₂.mem a) ∧
    (∀ d < m,
      denseQuotAt U V w N s₁ d = denseQuotAt U V w N s₂ d ∧
      denseValAt U V w N s₁ d = denseValAt U V w N s₂ d) := by
  refine ⟨?_, ?_⟩
  · intro a ha
    apply word_eq_of_readBit_eq hw (hs₁.mem_fits a) (hs₂.mem_fits a)
    intro j hj
    have hi_lt : a * w + j < dictBitSize U V w N m := by
      have h1 : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      rw [Nat.add_one_mul] at h1
      unfold dictBitSize epochMetaBits
      omega
    exact hbit (a * w + j) hi_lt
  · intro d hd
    have hd_end : itemBitOff U V w N (d + 1) ≤ dictBitSize U V w N m := by
      have h1 : (d + 1) * itemBits U V N ≤ m * itemBits U V N := Nat.mul_le_mul_right _ hd
      unfold itemBitOff dictBitSize
      omega
    have hq_end : itemQuotBitOff U V w N d + quotientBits U N ≤ dictBitSize U V w N m := by
      rw [itemBitOff_succ] at hd_end
      unfold itemQuotBitOff
      unfold itemBits at hd_end
      omega
    have hv_end : itemValBitOff U V w N d + valBits V ≤ dictBitSize U V w N m := by
      rwa [itemValBitOff_add_valBits]
    refine ⟨?_, ?_⟩
    · unfold denseQuotAt BitMemory.State.getField
      exact readField_congr_bits hw (quotientBits_le_of_le_pow hU) fun j hj =>
        hbit _ (by omega)
    · unfold denseValAt BitMemory.State.getField
      exact readField_congr_bits hw (valBits_le_of_le_pow hV) fun j hj =>
        hbit _ (by omega)

/-- Updating a metadata word `a < epochMetaWords U w N` does not affect `readField` at any bit
offset `off ≥ epochMetaBits U w N`. -/
theorem readField_update_of_lt_epochMetaWords {U w N a val off b : ℕ}
    (hw : 0 < w) (ha : a < epochMetaWords U w N) (hoff : epochMetaBits U w N ≤ off)
    (mem : ℕ → ℕ) :
    readField w 0 (Function.update mem a val) off b = readField w 0 mem off b := by
  have hdiv : epochMetaWords U w N ≤ off / w := by
    rw [Nat.le_div_iff_mul_le hw]
    unfold epochMetaBits at hoff
    omega
  have hne0 : 0 + off / w ≠ a := by omega
  have hne1 : 0 + off / w + 1 ≠ a := by omega
  unfold readField
  dsimp only
  rw [Function.update_of_ne hne0, Function.update_of_ne hne1]

/-- Concrete `BitRAM.Code .standard 12` program growing `bitSize` by `itemBits U V N` bits in `4`
instructions (`quotientBits U N` followed by `valBits V`). -/
@[expose]
def growItemCode (U V N : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 (quotientBits U N)))
    (.seq (.grow 1 1)
      (.seq (.op (.const 1 (valBits V)))
        (.grow 1 1)))

/-- Execution certificate for `growItemCode`: grows `bitSize` from `dictBitSize U V w N m` to
`dictBitSize U V w N (m + 1)` in `4` instructions under demonic `.grow`, preserving all metadata
words `< epochMetaWords U w N` and all existing dense items `< m`. -/
theorem growItemCode_exec {U V w N m : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hsz : x.bitSize = dictBitSize U V w N m)
    (hfit : Fits w (dictBitSize U V w N (m + 1))) :
    BitRAM.DemonicExecWithin w (growItemCode U V N) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = dictBitSize U V w N (m + 1) ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ d < m,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d)) 4 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hsz_succ : dictBitSize U V w N (m + 1) =
      dictBitSize U V w N m + quotientBits U N + valBits V := by
    unfold dictBitSize itemBits
    ring
  have hfit_q : Fits w (x.bitSize + quotientBits U N) := by
    refine Fits.of_le hfit ?_
    rw [hsz, hsz_succ]
    omega
  have hcost_q : max 1 (quotientBits U N ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hqw x.toBitMemoryState).le
  refine DemonicExecWithin.step_const (T := 3) hq_fits ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow (quotientBits U N)) s₁ x.bitSize ∧
        y₁ = ⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 2)
    (.grow hfit_q hcost_q fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  let x₁ : BitRAM.Data 12 :=
    ⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize, s₁.mem, s₁.bitSize⟩
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (quotientBits U N)) hw hx.mem_wf hfit_q hs₁
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hx.mem_wf.bitSize_fits
    · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  obtain ⟨hs₁_sz_raw, _, _, hpres₁, _⟩ := hs₁
  change s₁.bitSize = x.bitSize + quotientBits U N at hs₁_sz_raw
  have hfit_v : Fits w (x₁.bitSize + valBits V) := by
    change Fits w (s₁.bitSize + valBits V)
    rw [hs₁_sz_raw, hsz, ← hsz_succ]
    exact hfit
  have hcost_v : max 1 (valBits V ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hvw x₁.toBitMemoryState).le
  refine DemonicExecWithin.step_const (T := 1) hv_fits ?_
  refine DemonicExecWithin.grow hfit_v hcost_v (fun s₂ hs₂ => ?_)
  have hs₂_wf : s₂.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (valBits V)) hw hs₁_wf hfit_v hs₂
  let y : BitRAM.Data 12 :=
    ⟨Function.update (x₁.set 1 (valBits V)).regs 1 x₁.bitSize, s₂.mem, s₂.bitSize⟩
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hs₂_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hs₁_wf.bitSize_fits
    · simp only [y, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx₁_wf.regs_fits i
  obtain ⟨hs₂_sz_raw, _, _, hpres₂, _⟩ := hs₂
  change s₂.bitSize = s₁.bitSize + valBits V at hs₂_sz_raw
  have hy_sz : y.bitSize = dictBitSize U V w N (m + 1) := by
    change s₂.bitSize = dictBitSize U V w N (m + 1)
    rw [hs₂_sz_raw, hs₁_sz_raw, hsz, hsz_succ]
  have hbit : ∀ i < dictBitSize U V w N m,
      y.toBitMemoryState.getBit w i = x.toBitMemoryState.getBit w i := by
    intro i hi
    have hi_x : i < x.bitSize := by rw [hsz]; exact hi
    have hi_s1 : i < s₁.bitSize := by rw [hs₁_sz_raw]; omega
    exact (hpres₂ i hi_s1).trans (hpres₁ i hi_x)
  obtain ⟨hmeta, hitems⟩ :=
    preserve_meta_and_items_of_getBit_eq hw hU hV hy_wf.mem_wf hx.mem_wf hbit
  exact ⟨hy_wf, hy_sz, hmeta, hitems⟩

/-- Concrete `BitRAM.Code .standard 12` program shrinking `bitSize` by `itemBits U V N` bits in `4`
instructions (`valBits V` followed by `quotientBits U N`). -/
@[expose]
def shrinkItemCode (U V N : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 (valBits V)))
    (.seq (.shrink 1)
      (.seq (.op (.const 1 (quotientBits U N)))
        (.shrink 1)))

/-- Execution certificate for `shrinkItemCode`: shrinks `bitSize` from `dictBitSize U V w N (m + 1)`
to `dictBitSize U V w N m` in `4` instructions, preserving all metadata words
`< epochMetaWords U w N` and all dense items `< m`. -/
theorem shrinkItemCode_exec {U V w N m : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hsz : x.bitSize = dictBitSize U V w N (m + 1)) :
    BitRAM.DemonicExecWithin w (shrinkItemCode U V N) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = dictBitSize U V w N m ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ d < m,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d)) 4 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hsz_succ : dictBitSize U V w N (m + 1) =
      dictBitSize U V w N m + quotientBits U N + valBits V := by
    unfold dictBitSize itemBits
    ring
  have hv_le : valBits V ≤ x.bitSize := by
    rw [hsz, hsz_succ]; omega
  have hcost_v : max 1 (valBits V ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hvw x.toBitMemoryState).le
  set s₁ := (BitMemory.stepFn w x.toBitMemoryState (.shrink (valBits V))).1
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (valBits V)) hw hx.mem_wf hv_le
  have hs₁_sz : s₁.bitSize = dictBitSize U V w N m + quotientBits U N := by
    change x.bitSize - valBits V = _
    rw [hsz, hsz_succ]
    omega
  refine DemonicExecWithin.step_const (T := 3) hv_fits ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      y₁ = ⟨(x.set 1 (valBits V)).regs, s₁.mem, x.bitSize - valBits V⟩)
    (T₁ := 1) (T₂ := 2)
    (.shrink hv_le hcost_v rfl)
    (fun y₁ hy₁_eq => ?_) (by omega)
  subst hy₁_eq
  let x₁ : BitRAM.Data 12 := ⟨(x.set 1 (valBits V)).regs, s₁.mem, x.bitSize - valBits V⟩
  have hx₁_wf : x₁.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hv_fits
    · simp only [x₁, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  have hq_le : quotientBits U N ≤ x₁.bitSize := by
    change quotientBits U N ≤ s₁.bitSize
    rw [hs₁_sz]; omega
  have hcost_q : max 1 (quotientBits U N ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hqw x₁.toBitMemoryState).le
  set s₂ := (BitMemory.stepFn w x₁.toBitMemoryState (.shrink (quotientBits U N))).1
  have hs₂_wf : s₂.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (quotientBits U N)) hw hs₁_wf hq_le
  have hs₂_sz : s₂.bitSize = dictBitSize U V w N m := by
    change s₁.bitSize - quotientBits U N = _
    rw [hs₁_sz]
    omega
  refine DemonicExecWithin.step_const (T := 1) hq_fits ?_
  refine DemonicExecWithin.shrink hq_le hcost_q ?_
  let y : BitRAM.Data 12 :=
    ⟨(x₁.set 1 (quotientBits U N)).regs, s₂.mem, x₁.bitSize - quotientBits U N⟩
  have hy_wf : y.WellFormed w := by
    refine ⟨fun i => ?_, hs₂_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hq_fits
    · simp only [y, BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx₁_wf.regs_fits i
  have hbit : ∀ i < dictBitSize U V w N m,
      y.toBitMemoryState.getBit w i = x.toBitMemoryState.getBit w i := by
    intro i hi
    have hi_s2 : i < x₁.toBitMemoryState.bitSize - quotientBits U N := by
      change i < s₁.bitSize - quotientBits U N
      rw [hs₁_sz]; omega
    have hi_s1 : i < x.toBitMemoryState.bitSize - valBits V := by
      change i < x.bitSize - valBits V
      rw [hsz, hsz_succ]; omega
    have h1 := BitMemory.getBit_stepFn_shrink_of_lt hw x₁.toBitMemoryState (quotientBits U N) hi_s2
    have h2 := BitMemory.getBit_stepFn_shrink_of_lt hw x.toBitMemoryState (valBits V) hi_s1
    exact h1.trans h2
  obtain ⟨hmeta, hitems⟩ :=
    preserve_meta_and_items_of_getBit_eq hw hU hV hy_wf.mem_wf hx.mem_wf hbit
  exact ⟨hy_wf, hs₂_sz, hmeta, hitems⟩

/-! ## Section 2: Metadata word and dense item synchronization programs -/

/-- Synchronize a list `as : List ℕ` of metadata word addresses (`a < epochMetaWords U w N`) to
match `s_tar.mem`. -/
@[expose]
def syncMetaWordsListCode (s_tar : BitMemory.State) : List ℕ → BitRAM.Code .standard 12
  | [] => .op (.const 0 0)
  | a :: as =>
    .seq (storeWordCode a (s_tar.mem a))
      (syncMetaWordsListCode s_tar as)

/-- Execution certificate for `syncMetaWordsListCode`: executes in `1 + 3 * as.length` instructions,
setting `y.mem a = s_tar.mem a` for all `a ∈ as`, preserving `y.mem a = x.mem a` for all `a ∉ as`,
and preserving `bitSize` and all dense items. -/
theorem syncMetaWordsListCode_exec {U V w N : ℕ} (s_tar : BitMemory.State) (as : List ℕ)
    {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (has : ∀ a ∈ as, a < epochMetaWords U w N)
    (hsz : epochMetaBits U w N ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (syncMetaWordsListCode s_tar as) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = x.bitSize ∧
        (∀ a ∈ as, y.mem a = s_tar.mem a) ∧
        (∀ a, a ∉ as → y.mem a = x.mem a) ∧
        (∀ d,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d))
      (1 + 3 * as.length) := by
  induction as generalizing x with
  | nil =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    refine ⟨hy_wf, rfl, ?_, ?_, fun _ => ⟨rfl, rfl⟩⟩
    · intro a ha; cases ha
    · intro a _; rfl
  | cons a as' ih =>
    have ha_lt : a < epochMetaWords U w N := has a List.mem_cons_self
    have has' : ∀ a' ∈ as', a' < epochMetaWords U w N :=
      fun a' ha' => has a' (List.mem_cons_of_mem a ha')
    have ha_sz : (a + 1) * w ≤ x.bitSize := by
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha_lt
      unfold epochMetaBits at hsz
      omega
    refine .seq (T₁ := 3) (T₂ := 1 + 3 * as'.length)
      (storeWordCode_exec hw hx ha_sz (htar.mem_fits a))
      (fun y₁ ⟨hy₁_st, hy₁_wf, hy₁_sz⟩ => ?_)
      (by simp only [List.length_cons]; omega)
    have hy₁_mem : y₁.mem = Function.update x.mem a (s_tar.mem a) :=
      congrArg BitMemory.State.mem hy₁_st
    have hsz₁ : epochMetaBits U w N ≤ y₁.bitSize := by rw [hy₁_sz]; exact hsz
    refine (ih hy₁_wf has' hsz₁).mono
      (fun y ⟨hy_wf, hy_sz, hy_in, hy_out, hy_items⟩ => ?_) le_rfl
    refine ⟨hy_wf, hy_sz.trans hy₁_sz, ?_, ?_, ?_⟩
    · intro a' ha'
      by_cases hin' : a' ∈ as'
      · exact hy_in a' hin'
      · rcases List.mem_cons.mp ha' with rfl | hmem'
        · rw [hy_out a' hin', hy₁_mem, Function.update_self]
        · exact absurd hmem' hin'
    · intro a' hnot
      have hnot_head : a' ≠ a := fun h => hnot (h ▸ List.mem_cons_self)
      have hnot_tail : a' ∉ as' := fun h => hnot (List.mem_cons_of_mem a h)
      rw [hy_out a' hnot_tail, hy₁_mem, Function.update_of_ne hnot_head]
    · intro d
      have hq_off : epochMetaBits U w N ≤ itemQuotBitOff U V w N d := by
        unfold itemQuotBitOff itemBitOff; omega
      have hv_off : epochMetaBits U w N ≤ itemValBitOff U V w N d := by
        unfold itemValBitOff itemBitOff; omega
      have hq₁ : denseQuotAt U V w N y₁.toBitMemoryState d =
          denseQuotAt U V w N x.toBitMemoryState d := by
        unfold denseQuotAt BitMemory.State.getField
        change readField w 0 y₁.mem _ _ = readField w 0 x.mem _ _
        rw [hy₁_mem, readField_update_of_lt_epochMetaWords hw ha_lt hq_off]
      have hv₁ : denseValAt U V w N y₁.toBitMemoryState d =
          denseValAt U V w N x.toBitMemoryState d := by
        unfold denseValAt BitMemory.State.getField
        change readField w 0 y₁.mem _ _ = readField w 0 x.mem _ _
        rw [hy₁_mem, readField_update_of_lt_epochMetaWords hw ha_lt hv_off]
      exact ⟨(hy_items d).1.trans hq₁, (hy_items d).2.trans hv₁⟩

/-- Synchronize a list `ds : List ℕ` of dense item indices (`d < m`) to match `s_tar`. -/
@[expose]
def syncDenseItemsListCode (U V w N : ℕ) (s_tar : BitMemory.State) :
    List ℕ → BitRAM.Code .standard 12
  | [] => .op (.const 0 0)
  | d :: ds =>
    .seq (writeDenseItemCode U V w N d
        (denseQuotAt U V w N s_tar d) (denseValAt U V w N s_tar d))
      (syncDenseItemsListCode U V w N s_tar ds)

/-- Execution certificate for `syncDenseItemsListCode`: executes in `1 + 90 * ds.length`
instructions, setting dense item `d` to match `s_tar` for all `d ∈ ds`, preserving dense item `d`
for all `d < m` with `d ∉ ds`, and preserving `bitSize` and all metadata words
`< epochMetaWords U w N`. -/
theorem syncDenseItemsListCode_exec {U V w N m : ℕ} (s_tar : BitMemory.State) (ds : List ℕ)
    {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hds : ∀ d ∈ ds, d < m)
    (hsz : dictBitSize U V w N m ≤ x.bitSize) :
    BitRAM.DemonicExecWithin w (syncDenseItemsListCode U V w N s_tar ds) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = x.bitSize ∧
        (∀ d ∈ ds,
          denseQuotAt U V w N y.toBitMemoryState d = denseQuotAt U V w N s_tar d ∧
          denseValAt U V w N y.toBitMemoryState d = denseValAt U V w N s_tar d) ∧
        (∀ d < m, d ∉ ds →
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a))
      (1 + 90 * ds.length) := by
  induction ds generalizing x with
  | nil =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    refine ⟨hy_wf, rfl, ?_, fun _ _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl⟩
    intro d hd; cases hd
  | cons d ds' ih =>
    have hd_lt : d < m := hds d List.mem_cons_self
    have hds' : ∀ d' ∈ ds', d' < m := fun d' hd' => hds d' (List.mem_cons_of_mem d hd')
    have hq_fits : Fits (quotientBits U N) (denseQuotAt U V w N s_tar d) :=
      denseQuotAt_lt U V w N s_tar d
    have hv_fits : Fits (valBits V) (denseValAt U V w N s_tar d) :=
      denseValAt_lt U V w N s_tar d
    refine .seq (T₁ := 90) (T₂ := 1 + 90 * ds'.length)
      (writeDenseItemCode_exec hw hU hV hx hd_lt hsz hq_fits hv_fits)
      (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_q, hy₁_v, hy₁_other, hy₁_meta⟩ => ?_)
      (by simp only [List.length_cons]; omega)
    have hsz₁ : dictBitSize U V w N m ≤ y₁.bitSize := by rw [hy₁_sz]; exact hsz
    refine (ih hy₁_wf hds' hsz₁).mono
      (fun y ⟨hy_wf, hy_sz, hy_in, hy_out, hy_meta⟩ => ?_) le_rfl
    refine ⟨hy_wf, hy_sz.trans hy₁_sz, ?_, ?_, ?_⟩
    · intro d' hd'
      by_cases hin' : d' ∈ ds'
      · exact hy_in d' hin'
      · rcases List.mem_cons.mp hd' with rfl | hmem'
        · have hpreserve := hy_out d' hd_lt hin'
          exact ⟨hpreserve.1.trans hy₁_q, hpreserve.2.trans hy₁_v⟩
        · exact absurd hmem' hin'
    · intro d' hd'_lt hnot
      have hnot_head : d' ≠ d := fun h => hnot (h ▸ List.mem_cons_self)
      have hnot_tail : d' ∉ ds' := fun h => hnot (List.mem_cons_of_mem d h)
      have h1 := hy_out d' hd'_lt hnot_tail
      have h2 := hy₁_other d' hd'_lt hnot_head
      exact ⟨h1.1.trans h2.1, h1.2.trans h2.2⟩
    · intro a ha
      exact (hy_meta a ha).trans (hy₁_meta a ha)

/-- List of metadata word addresses `< epochMetaWords U w N` where `s_cur.mem a ≠ s_tar.mem a`. -/
@[expose]
def changedMetaList (U w N : ℕ) (s_cur s_tar : BitMemory.State) : List ℕ :=
  (List.range (epochMetaWords U w N)).filter (fun a => decide (s_cur.mem a ≠ s_tar.mem a))

/-- List of dense item indices `< m` where `(denseQuotAt, denseValAt)` differs between `s_cur` and
`s_tar`. -/
@[expose]
def changedDenseList (U V w N m : ℕ) (s_cur s_tar : BitMemory.State) : List ℕ :=
  (List.range m).filter (fun d =>
    decide (denseQuotAt U V w N s_cur d ≠ denseQuotAt U V w N s_tar d ∨
      denseValAt U V w N s_cur d ≠ denseValAt U V w N s_tar d))

/-! ## Section 3: In-epoch and rebuild state-synchronization programs -/

/-- Concrete `BitRAM.Code .standard 12` program synchronizing an in-epoch insertion (`m → m + 1`)
from `s_cur` to `s_tar`. -/
@[expose]
def inEpochInsertSyncCode (U V w N m : ℕ) (s_cur s_tar : BitMemory.State) :
    BitRAM.Code .standard 12 :=
  .seq (growItemCode U V N)
    (.seq (writeDenseItemCode U V w N m
        (denseQuotAt U V w N s_tar m) (denseValAt U V w N s_tar m))
      (.seq (syncDenseItemsListCode U V w N s_tar (changedDenseList U V w N m s_cur s_tar))
        (syncMetaWordsListCode s_tar (changedMetaList U w N s_cur s_tar))))

/-- Execution certificate for `inEpochInsertSyncCode`: executes under demonic `.grow` in
`96 + 90 * (changedDenseList ...).length + 3 * (changedMetaList ...).length` instructions,
producing `y.toBitMemoryState = s_tar`. -/
theorem inEpochInsertSyncCode_exec {U V w N m : ℕ} {x : BitRAM.Data 12}
    (s_tar : BitMemory.State)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N m)
    (htar_sz : s_tar.bitSize = dictBitSize U V w N (m + 1)) :
    BitRAM.DemonicExecWithin w
      (inEpochInsertSyncCode U V w N m x.toBitMemoryState s_tar) x
      (fun y => y.toBitMemoryState = s_tar ∧ y.WellFormed w)
      (96 + 90 * (changedDenseList U V w N m x.toBitMemoryState s_tar).length +
        3 * (changedMetaList U w N x.toBitMemoryState s_tar).length) := by
  set ds := changedDenseList U V w N m x.toBitMemoryState s_tar
  set as := changedMetaList U w N x.toBitMemoryState s_tar
  have hfit_tar : Fits w (dictBitSize U V w N (m + 1)) := by
    rw [← htar_sz]; exact htar.bitSize_fits
  have hds_lt : ∀ d ∈ ds, d < m + 1 := by
    intro d hd
    have hd_m : d < m := List.mem_range.mp (List.mem_of_mem_filter hd)
    omega
  have has_lt : ∀ a ∈ as, a < epochMetaWords U w N :=
    fun a ha => List.mem_range.mp (List.mem_of_mem_filter ha)
  refine .seq (T₁ := 4) (T₂ := 92 + 90 * ds.length + 3 * as.length)
    (growItemCode_exec hw hU hV hx hx_sz hfit_tar)
    (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_meta, hy₁_items⟩ => ?_) (by omega)
  have hm_lt : m < m + 1 := Nat.lt_succ_self m
  have hq_m : Fits (quotientBits U N) (denseQuotAt U V w N s_tar m) :=
    denseQuotAt_lt U V w N s_tar m
  have hv_m : Fits (valBits V) (denseValAt U V w N s_tar m) :=
    denseValAt_lt U V w N s_tar m
  refine .seq (T₁ := 90) (T₂ := 2 + 90 * ds.length + 3 * as.length)
    (writeDenseItemCode_exec hw hU hV hy₁_wf hm_lt hy₁_sz.symm.le hq_m hv_m)
    (fun y₂ ⟨hy₂_wf, hy₂_sz, hy₂_qm, hy₂_vm, hy₂_other, hy₂_meta⟩ => ?_) (by omega)
  have hy₂_sz_eq : y₂.bitSize = dictBitSize U V w N (m + 1) := hy₂_sz.trans hy₁_sz
  refine .seq (T₁ := 1 + 90 * ds.length) (T₂ := 1 + 3 * as.length)
    (syncDenseItemsListCode_exec s_tar ds hw hU hV hy₂_wf hds_lt hy₂_sz_eq.symm.le)
    (fun y₃ ⟨hy₃_wf, hy₃_sz, hy₃_in, hy₃_out, hy₃_meta⟩ => ?_) (by omega)
  have hy₃_sz_eq : y₃.bitSize = dictBitSize U V w N (m + 1) := hy₃_sz.trans hy₂_sz_eq
  have hmeta_le₃ : epochMetaBits U w N ≤ y₃.bitSize := by
    rw [hy₃_sz_eq]; unfold dictBitSize; omega
  refine (syncMetaWordsListCode_exec (U := U) (V := V) s_tar as
    hw hy₃_wf htar has_lt hmeta_le₃).mono
    (fun y ⟨hy_wf, hy_sz, hy_in, hy_out, hy_items⟩ => ?_) le_rfl
  have hy_sz_eq : y.bitSize = dictBitSize U V w N (m + 1) := hy_sz.trans hy₃_sz_eq
  refine ⟨?_, hy_wf⟩
  apply bitMemoryState_eq_of_meta_and_items hw hU hV hy_wf.mem_wf htar hy_sz_eq htar_sz
  · intro a ha
    by_cases hin : a ∈ as
    · exact hy_in a hin
    · have h1 := hy_out a hin
      have h2 := (hy₃_meta a ha).trans ((hy₂_meta a ha).trans (hy₁_meta a ha))
      have heq : x.mem a = s_tar.mem a := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr ha, decide_eq_true hne⟩)
      exact h1.trans (h2.trans heq)
  · intro d hd
    have hitem_y := hy_items d
    rw [hitem_y.1, hitem_y.2]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd_m | rfl
    · by_cases hin : d ∈ ds
      · exact hy₃_in d hin
      · have h1 := hy₃_out d hd hin
        have h2 := hy₂_other d hd (Nat.ne_of_lt hd_m)
        have h3 := hy₁_items d hd_m
        have heq_q : denseQuotAt U V w N x.toBitMemoryState d = denseQuotAt U V w N s_tar d := by
          by_contra hne
          exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd_m, decide_eq_true (Or.inl hne)⟩)
        have heq_v : denseValAt U V w N x.toBitMemoryState d = denseValAt U V w N s_tar d := by
          by_contra hne
          exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd_m, decide_eq_true (Or.inr hne)⟩)
        exact ⟨h1.1.trans (h2.1.trans (h3.1.trans heq_q)),
          h1.2.trans (h2.2.trans (h3.2.trans heq_v))⟩
    · have hnot_in : d ∉ ds := by
        intro hin
        have : d < d := List.mem_range.mp (List.mem_of_mem_filter hin)
        omega
      have h1 := hy₃_out d hd hnot_in
      exact ⟨h1.1.trans hy₂_qm, h1.2.trans hy₂_vm⟩

/-- Concrete `BitRAM.Code .standard 12` program synchronizing an in-epoch deletion (`m + 1 → m`)
from `s_cur` to `s_tar`. -/
@[expose]
def inEpochDeleteSyncCode (U V w N m : ℕ) (s_cur s_tar : BitMemory.State) :
    BitRAM.Code .standard 12 :=
  .seq (syncDenseItemsListCode U V w N s_tar (changedDenseList U V w N m s_cur s_tar))
    (.seq (syncMetaWordsListCode s_tar (changedMetaList U w N s_cur s_tar))
      (shrinkItemCode U V N))

/-- Execution certificate for `inEpochDeleteSyncCode`: executes in
`6 + 90 * (changedDenseList ...).length + 3 * (changedMetaList ...).length` instructions,
shrinking `bitSize` to `dictBitSize U V w N m` and producing `y.toBitMemoryState = s_tar`. -/
theorem inEpochDeleteSyncCode_exec {U V w N m : ℕ} {x : BitRAM.Data 12}
    (s_tar : BitMemory.State)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N (m + 1))
    (htar_sz : s_tar.bitSize = dictBitSize U V w N m) :
    BitRAM.DemonicExecWithin w
      (inEpochDeleteSyncCode U V w N m x.toBitMemoryState s_tar) x
      (fun y => y.toBitMemoryState = s_tar ∧ y.WellFormed w)
      (6 + 90 * (changedDenseList U V w N m x.toBitMemoryState s_tar).length +
        3 * (changedMetaList U w N x.toBitMemoryState s_tar).length) := by
  set ds := changedDenseList U V w N m x.toBitMemoryState s_tar
  set as := changedMetaList U w N x.toBitMemoryState s_tar
  have hds_lt : ∀ d ∈ ds, d < m :=
    fun d hd => List.mem_range.mp (List.mem_of_mem_filter hd)
  have has_lt : ∀ a ∈ as, a < epochMetaWords U w N :=
    fun a ha => List.mem_range.mp (List.mem_of_mem_filter ha)
  have hsz_le : dictBitSize U V w N m ≤ x.bitSize := by
    rw [hx_sz]; unfold dictBitSize
    have : m * itemBits U V N ≤ (m + 1) * itemBits U V N :=
      Nat.mul_le_mul_right _ (Nat.le_succ m)
    omega
  refine .seq (T₁ := 1 + 90 * ds.length) (T₂ := 5 + 3 * as.length)
    (syncDenseItemsListCode_exec s_tar ds hw hU hV hx hds_lt hsz_le)
    (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_in, hy₁_out, hy₁_meta⟩ => ?_) (by omega)
  have hmeta_le₁ : epochMetaBits U w N ≤ y₁.bitSize := by
    rw [hy₁_sz, hx_sz]; unfold dictBitSize; omega
  refine .seq (T₁ := 1 + 3 * as.length) (T₂ := 4)
    (syncMetaWordsListCode_exec (U := U) (V := V) s_tar as hw hy₁_wf htar has_lt hmeta_le₁)
    (fun y₂ ⟨hy₂_wf, hy₂_sz, hy₂_in, hy₂_out, hy₂_items⟩ => ?_) (by omega)
  have hy₂_sz_eq : y₂.bitSize = dictBitSize U V w N (m + 1) :=
    hy₂_sz.trans (hy₁_sz.trans hx_sz)
  refine (shrinkItemCode_exec hw hU hV hy₂_wf hy₂_sz_eq).mono
    (fun y ⟨hy_wf, hy_sz, hy_meta, hy_items⟩ => ?_) le_rfl
  refine ⟨?_, hy_wf⟩
  apply bitMemoryState_eq_of_meta_and_items hw hU hV hy_wf.mem_wf htar hy_sz htar_sz
  · intro a ha
    change y.mem a = s_tar.mem a
    rw [hy_meta a ha]
    by_cases hin : a ∈ as
    · exact hy₂_in a hin
    · have h1 := hy₂_out a hin
      have h2 := hy₁_meta a ha
      have heq : x.mem a = s_tar.mem a := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr ha, decide_eq_true hne⟩)
      exact h1.trans (h2.trans heq)
  · intro d hd
    have h1 := hy_items d hd
    have h2 := hy₂_items d
    rw [h1.1, h1.2, h2.1, h2.2]
    by_cases hin : d ∈ ds
    · exact hy₁_in d hin
    · have h3 := hy₁_out d hd hin
      have heq_q : denseQuotAt U V w N x.toBitMemoryState d = denseQuotAt U V w N s_tar d := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd, decide_eq_true (Or.inl hne)⟩)
      have heq_v : denseValAt U V w N x.toBitMemoryState d = denseValAt U V w N s_tar d := by
        by_contra hne
        exact hin (List.mem_filter.mpr ⟨List.mem_range.mpr hd, decide_eq_true (Or.inr hne)⟩)
      exact ⟨h3.1.trans heq_q, h3.2.trans heq_v⟩

/-- Shrink `m` dense items from the top of `bitSize` (`dictBitSize U V w N m → epochMetaBits U w N`)
in `1 + 4 * m` instructions. -/
@[expose]
def shrinkItemsCountCode (U V N : ℕ) : ℕ → BitRAM.Code .standard 12
  | 0 => .op (.const 0 0)
  | m + 1 =>
    .seq (shrinkItemCode U V N)
      (shrinkItemsCountCode U V N m)

theorem shrinkItemsCountCode_exec {U V w N : ℕ} (m : ℕ) {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hsz : x.bitSize = dictBitSize U V w N m) :
    BitRAM.DemonicExecWithin w (shrinkItemsCountCode U V N m) x
      (fun y => y.WellFormed w ∧ y.bitSize = epochMetaBits U w N)
      (1 + 4 * m) := by
  induction m generalizing x with
  | zero =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    refine ⟨hy_wf, ?_⟩
    change x.bitSize = epochMetaBits U w N
    simpa [dictBitSize] using hsz
  | succ m' ih =>
    refine .seq (T₁ := 4) (T₂ := 1 + 4 * m')
      (shrinkItemCode_exec hw hU hV hx hsz)
      (fun y₁ ⟨hy₁_wf, hy₁_sz, _, _⟩ => ih hy₁_wf hy₁_sz)
      (by omega)

/-- Shrink `k` full `w`-bit words (`k * w → 0`) in `1 + 2 * k` instructions. -/
@[expose]
def shrinkWordsCountCode (w : ℕ) : ℕ → BitRAM.Code .standard 12
  | 0 => .op (.const 0 0)
  | k + 1 =>
    .seq (shrinkWordCode w)
      (shrinkWordsCountCode w k)

theorem shrinkWordsCountCode_exec {w : ℕ} (k : ℕ) {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (hsz : x.bitSize = k * w) :
    BitRAM.DemonicExecWithin w (shrinkWordsCountCode w k) x
      (fun y => y.WellFormed w ∧ y.bitSize = 0)
      (1 + 2 * k) := by
  induction k generalizing x with
  | zero =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    exact ⟨hy_wf, by simpa using hsz⟩
  | succ k' ih =>
    refine .seq (T₁ := 2) (T₂ := 1 + 2 * k')
      (shrinkWordCode_exec hw hx hsz)
      (fun y₁ ⟨hy₁_wf, hy₁_sz, _⟩ => ih hy₁_wf hy₁_sz)
      (by omega)

/-- Grow `k` full `w`-bit words (`0 → k * w`) and store `s_tar.mem 0 .. s_tar.mem (k - 1)` in
`1 + 5 * k` instructions under demonic `.grow`. -/
@[expose]
def growWordsRangeCode (w : ℕ) (s_tar : BitMemory.State) : ℕ → BitRAM.Code .standard 12
  | 0 => .op (.const 0 0)
  | k + 1 =>
    .seq (growWordsRangeCode w s_tar k)
      (growWordStoreCode w k (s_tar.mem k))

theorem growWordsRangeCode_exec {w : ℕ} (s_tar : BitMemory.State) (k : ℕ)
    {x : BitRAM.Data 12}
    (hw : 0 < w) (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hsz : x.bitSize = 0) (hfit : Fits w (k * w)) :
    BitRAM.DemonicExecWithin w (growWordsRangeCode w s_tar k) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = k * w ∧
        (∀ a < k, y.mem a = s_tar.mem a))
      (1 + 5 * k) := by
  induction k with
  | zero =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    exact ⟨hy_wf, by simpa using hsz, fun a ha => by omega⟩
  | succ k' ih =>
    have hfit' : Fits w (k' * w) :=
      Fits.of_le hfit (Nat.mul_le_mul_right w (Nat.le_succ k'))
    refine .seq (T₁ := 1 + 5 * k') (T₂ := 5)
      (ih hfit')
      (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_mem⟩ => ?_)
      (by omega)
    refine (growWordStoreCode_exec hw hy₁_wf hy₁_sz hfit (htar.mem_fits k')).mono
      (fun y ⟨hy_st, hy_wf, hy_sz⟩ => ?_) le_rfl
    have hy_mem_eq : y.mem = Function.update y₁.mem k' (s_tar.mem k') :=
      congrArg BitMemory.State.mem hy_st
    refine ⟨hy_wf, hy_sz, ?_⟩
    intro a ha
    rw [hy_mem_eq]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ha')]
      exact hy₁_mem a ha'
    · rw [Function.update_self]

/-- Append `m` dense items `0 .. m - 1` from `s_tar` on top of `epochMetaBits U w N'` in
`1 + 94 * m` instructions under demonic `.grow`. -/
@[expose]
def appendItemsRangeCode (U V w N' : ℕ) (s_tar : BitMemory.State) :
    ℕ → BitRAM.Code .standard 12
  | 0 => .op (.const 0 0)
  | m + 1 =>
    .seq (appendItemsRangeCode U V w N' s_tar m)
      (.seq (growItemCode U V N')
        (writeDenseItemCode U V w N' m
          (denseQuotAt U V w N' s_tar m) (denseValAt U V w N' s_tar m)))

theorem appendItemsRangeCode_exec {U V w N' : ℕ} (s_tar : BitMemory.State) (m : ℕ)
    {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hsz : x.bitSize = epochMetaBits U w N')
    (hfit : Fits w (dictBitSize U V w N' m)) :
    BitRAM.DemonicExecWithin w (appendItemsRangeCode U V w N' s_tar m) x
      (fun y =>
        y.WellFormed w ∧
        y.bitSize = dictBitSize U V w N' m ∧
        (∀ a < epochMetaWords U w N', y.mem a = x.mem a) ∧
        (∀ d < m,
          denseQuotAt U V w N' y.toBitMemoryState d = denseQuotAt U V w N' s_tar d ∧
          denseValAt U V w N' y.toBitMemoryState d = denseValAt U V w N' s_tar d))
      (1 + 94 * m) := by
  induction m with
  | zero =>
    have h0 : Fits w 0 := fits_zero w
    refine DemonicExecWithin.const h0 ?_
    have hy_wf : (x.set 0 0).WellFormed w := by
      refine ⟨fun i => ?_, hx.mem_wf⟩
      by_cases hi0 : i = 0
      · subst hi0; exact h0
      · simp only [BitRAM.Data.set, Function.update_of_ne hi0]
        exact hx.regs_fits i
    exact ⟨hy_wf, by simpa [dictBitSize] using hsz, fun _ _ => rfl, fun d hd => by omega⟩
  | succ m' ih =>
    have hfit' : Fits w (dictBitSize U V w N' m') := by
      refine Fits.of_le hfit ?_
      unfold dictBitSize
      have : m' * itemBits U V N' ≤ (m' + 1) * itemBits U V N' :=
        Nat.mul_le_mul_right _ (Nat.le_succ m')
      omega
    refine .seq (T₁ := 1 + 94 * m') (T₂ := 94)
      (ih hfit')
      (fun y₁ ⟨hy₁_wf, hy₁_sz, hy₁_meta, hy₁_items⟩ => ?_)
      (by omega)
    refine .seq (T₁ := 4) (T₂ := 90)
      (growItemCode_exec hw hU hV hy₁_wf hy₁_sz hfit)
      (fun y₂ ⟨hy₂_wf, hy₂_sz, hy₂_meta, hy₂_items⟩ => ?_)
      (by omega)
    have hm'_lt : m' < m' + 1 := Nat.lt_succ_self m'
    have hq_fits : Fits (quotientBits U N') (denseQuotAt U V w N' s_tar m') :=
      denseQuotAt_lt U V w N' s_tar m'
    have hv_fits : Fits (valBits V) (denseValAt U V w N' s_tar m') :=
      denseValAt_lt U V w N' s_tar m'
    refine (writeDenseItemCode_exec hw hU hV hy₂_wf hm'_lt hy₂_sz.symm.le hq_fits hv_fits).mono
      (fun y ⟨hy_wf, hy_sz, hy_qm, hy_vm, hy_other, hy_meta⟩ => ?_) le_rfl
    refine ⟨hy_wf, hy_sz.trans hy₂_sz, ?_, ?_⟩
    · intro a ha
      exact (hy_meta a ha).trans ((hy₂_meta a ha).trans (hy₁_meta a ha))
    · intro d hd
      rcases Nat.lt_succ_iff_lt_or_eq.mp hd with hd' | rfl
      · have h1 := hy_other d hd (Nat.ne_of_lt hd')
        have h2 := hy₂_items d hd'
        have h3 := hy₁_items d hd'
        exact ⟨h1.1.trans (h2.1.trans h3.1), h1.2.trans (h2.2.trans h3.2)⟩
      · exact ⟨hy_qm, hy_vm⟩

/-- Concrete `BitRAM.Code .standard 12` program for an epoch rebuild from `(N, m)` to `(N', m')`
producing target state `s_tar`. -/
@[expose]
def rebuildSyncCode (U V w N m N' m' : ℕ) (s_tar : BitMemory.State) :
    BitRAM.Code .standard 12 :=
  .seq (shrinkItemsCountCode U V N m)
    (.seq (shrinkWordsCountCode w (epochMetaWords U w N))
      (.seq (growWordsRangeCode w s_tar (epochMetaWords U w N'))
        (appendItemsRangeCode U V w N' s_tar m')))

/-- Execution certificate for `rebuildSyncCode`: transitions from any well-formed state `x` with
`x.bitSize = dictBitSize U V w N m` to `y.toBitMemoryState = s_tar` in
`4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m'` instructions under
demonic `.grow`. -/
theorem rebuildSyncCode_exec {U V w N m N' m' : ℕ} {x : BitRAM.Data 12}
    (s_tar : BitMemory.State)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (htar : s_tar.WellFormed w)
    (hx_sz : x.bitSize = dictBitSize U V w N m)
    (htar_sz : s_tar.bitSize = dictBitSize U V w N' m') :
    BitRAM.DemonicExecWithin w (rebuildSyncCode U V w N m N' m' s_tar) x
      (fun y => y.toBitMemoryState = s_tar ∧ y.WellFormed w)
      (4 + 4 * m + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m') := by
  have hfit_tar : Fits w (dictBitSize U V w N' m') := by
    rw [← htar_sz]; exact htar.bitSize_fits
  have hfit_meta' : Fits w (epochMetaWords U w N' * w) := by
    refine Fits.of_le hfit_tar ?_
    unfold dictBitSize epochMetaBits
    omega
  refine .seq (T₁ := 1 + 4 * m)
    (T₂ := 3 + 2 * epochMetaWords U w N + 5 * epochMetaWords U w N' + 94 * m')
    (shrinkItemsCountCode_exec m hw hU hV hx hx_sz)
    (fun y₁ ⟨hy₁_wf, hy₁_sz⟩ => ?_) (by omega)
  refine .seq (T₁ := 1 + 2 * epochMetaWords U w N)
    (T₂ := 2 + 5 * epochMetaWords U w N' + 94 * m')
    (shrinkWordsCountCode_exec (epochMetaWords U w N) hw hy₁_wf hy₁_sz)
    (fun y₂ ⟨hy₂_wf, hy₂_sz⟩ => ?_) (by omega)
  refine .seq (T₁ := 1 + 5 * epochMetaWords U w N') (T₂ := 1 + 94 * m')
    (growWordsRangeCode_exec s_tar (epochMetaWords U w N') hw hy₂_wf htar hy₂_sz hfit_meta')
    (fun y₃ ⟨hy₃_wf, hy₃_sz, hy₃_mem⟩ => ?_) (by omega)
  refine (appendItemsRangeCode_exec s_tar m' hw hU hV hy₃_wf hy₃_sz hfit_tar).mono
    (fun y ⟨hy_wf, hy_sz, hy_meta, hy_items⟩ => ?_) le_rfl
  refine ⟨?_, hy_wf⟩
  apply bitMemoryState_eq_of_meta_and_items hw hU hV hy_wf.mem_wf htar hy_sz htar_sz
  · intro a ha
    exact (hy_meta a ha).trans (hy₃_mem a ha)
  · exact hy_items

end Cslib.DataStructure.Dictionary.BitResizable
