/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Query
public import Complexity.DataStructure.Dictionary.BitResizable.Operations

/-!
# Window-Coupled State Synchronization, Circular Window Programs, and `LocalMeta` Chain Programs

This module provides the uniform `BitRAM.Code .standard 280` building blocks for in-epoch
insertions, deletions, and slab promotions/demotions on the single-tape bit-resizable dictionary:
1. Dense item write and copy helpers (`writeDenseVRegCode_frame`, `writeDenseQVRegCode`,
   `copyDenseItemRegCode`) with full metadata and dense-item frame theorems.
2. Circular tail-to-dense window invariant (`WindowInv`) and functional window transitions
   (`winGrowRight`, `winGrowLeft`, `winShrinkRight`, `winShrinkLeft`) with `physByBase`
   correspondence lemmas.
3. Coupling predicates (`WindowCoupled`, `FixedCoupled`) between the fixed-capacity dictionary state
   `s_fix : Memory.State` and the bit-resizable state `s_bit : BitMemory.State`.
4. Uniform `BitRAM.Code .standard 280` programs for circular window updates
   (`denseOfTailRegCode`, `winGrowRightRegCode`, `winGrowLeftRegCode`, `winShrinkRightRegCode`,
   `winShrinkLeftRegCode`) and `LocalMeta` doubly-linked chain updates (`lmPrependRegCode`,
   `prependIfIndexedRegCode`, `lmUnlinkRegCode`, `unlinkIfIndexedRegCode`).
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

/-! ## Section 1: Dense item write and copy helpers with frame theorems -/

/-- Frame theorem for `writeDenseVRegCode`: writing value `v` at dense index `d < n_t` updates
`denseValAt ... d` to `v` and preserves `denseValAt ... d'` for `d' ≠ d`, all `denseQuotAt`,
and all metadata words `< epochMetaWords U w N`. -/
theorem writeDenseVRegCode_frame {U V w N n_t d v : ℕ} {rD rV : Fin 280} {x : BitRAM.Data 280}
    (hrD_ge : 16 ≤ rD.val) (hrV_ge : 16 ≤ rV.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d) (hrV : x.regs rV = v)
    (hv : Fits (valBits V) v)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (writeDenseVRegCode rD rV) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        denseValAt U V w N y.toBitMemoryState d = v ∧
        (∀ d' < n_t, d' ≠ d →
          denseValAt U V w N y.toBitMemoryState d' =
            denseValAt U V w N x.toBitMemoryState d') ∧
        (∀ d' < n_t,
          denseQuotAt U V w N y.toBitMemoryState d' =
            denseQuotAt U V w N x.toBitMemoryState d') ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 55 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  refine (writeDenseVRegCode_exec hrD_ge hrV_ge hw hV hx her hd hrD hrV hv hsz hm2 hm3).mono
    (fun y ⟨hy_st, hy_wf, hy_er, hy_regs⟩ => ?_) le_rfl
  have hy_mem : y.mem = writeFieldMem w 0 x.mem (itemValBitOff U V w N d) (valBits V) v :=
    congrArg BitMemory.State.mem hy_st
  have hy_sz : y.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy_st
  refine ⟨hy_wf, hy_er, hy_sz, ?_, ?_, ?_, ?_, hy_regs⟩
  · unfold denseValAt BitMemory.State.getField
    change readField w 0 y.mem (itemValBitOff U V w N d) (valBits V) = v
    rw [hy_mem, readField_writeFieldMem_same hw _ hvw hv]
  · intro d' _ hne
    have hdisj : itemValBitOff U V w N d' + valBits V ≤ itemValBitOff U V w N d ∨
        itemValBitOff U V w N d + valBits V ≤ itemValBitOff U V w N d' := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · left
        have : (d' + 1) * itemBits U V N ≤ d * itemBits U V N := Nat.mul_le_mul_right _ hlt
        rw [Nat.add_one_mul] at this
        unfold itemValBitOff itemBitOff itemBits; unfold itemBits at this; omega
      · right
        have : (d + 1) * itemBits U V N ≤ d' * itemBits U V N := Nat.mul_le_mul_right _ hgt
        rw [Nat.add_one_mul] at this
        unfold itemValBitOff itemBitOff itemBits; unfold itemBits at this; omega
    unfold denseValAt BitMemory.State.getField
    change readField w 0 y.mem _ _ = readField w 0 x.mem _ _
    rw [hy_mem, readField_writeFieldMem_of_disjoint hw _ hvw hvw hdisj]
  · intro d' _
    have hdisj : itemQuotBitOff U V w N d' + quotientBits U N ≤ itemValBitOff U V w N d ∨
        itemValBitOff U V w N d + valBits V ≤ itemQuotBitOff U V w N d' := by
      by_cases heq : d' = d
      · subst heq; left; unfold itemQuotBitOff itemValBitOff; omega
      · rcases lt_or_gt_of_ne heq with hlt | hgt
        · left
          have : (d' + 1) * itemBits U V N ≤ d * itemBits U V N := Nat.mul_le_mul_right _ hlt
          rw [Nat.add_one_mul] at this
          unfold itemQuotBitOff itemValBitOff itemBitOff itemBits; unfold itemBits at this; omega
        · right
          have : (d + 1) * itemBits U V N ≤ d' * itemBits U V N := Nat.mul_le_mul_right _ hgt
          rw [Nat.add_one_mul] at this
          unfold itemQuotBitOff itemValBitOff itemBitOff itemBits; unfold itemBits at this; omega
    unfold denseQuotAt BitMemory.State.getField
    change readField w 0 y.mem _ _ = readField w 0 x.mem _ _
    rw [hy_mem, readField_writeFieldMem_of_disjoint hw _ hvw hqw hdisj]
  · intro a ha
    have ha_bits : (a + 1) * w ≤ itemValBitOff U V w N d := by
      unfold itemValBitOff itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    rw [hy_mem]
    apply word_eq_of_readBit_eq hw
      (writeFieldMem_fits hw hx.mem_wf.mem_fits hvw v a) (hx.mem_wf.mem_fits a)
    intro j hj
    rw [readBit_writeFieldMem hw _ hvw (a * w + j)]
    have hnot : ¬(itemValBitOff U V w N d ≤ a * w + j ∧
        a * w + j < itemValBitOff U V w N d + valBits V) := by
      rw [Nat.add_one_mul] at ha_bits; omega
    rw [ite_eq_right hnot]

/-- Write both quotient `rQ` and value `rV` into dense item `rD` (`BitRAM.Code .standard 280`). -/
@[expose]
def writeDenseQVRegCode (rD rQ rV : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (writeDenseQRegCode rD rQ)
       (writeDenseVRegCode rD rV)

theorem writeDenseQVRegCode_exec {U V w N n_t d q v : ℕ} {rD rQ rV : Fin 280}
    {x : BitRAM.Data 280}
    (hrD_ge : 16 ≤ rD.val) (hrQ_ge : 16 ≤ rQ.val) (hrV_ge : 16 ≤ rV.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hd : d < n_t) (hrD : x.regs rD = d) (hrQ : x.regs rQ = q) (hrV : x.regs rV = v)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (writeDenseQVRegCode rD rQ rV) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        denseQuotAt U V w N y.toBitMemoryState d = q ∧
        denseValAt U V w N y.toBitMemoryState d = v ∧
        (∀ d' < n_t, d' ≠ d →
          denseQuotAt U V w N y.toBitMemoryState d' =
            denseQuotAt U V w N x.toBitMemoryState d' ∧
          denseValAt U V w N y.toBitMemoryState d' =
            denseValAt U V w N x.toBitMemoryState d') ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 16 ≤ r.val → y.regs r = x.regs r)) 108 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  unfold writeDenseQVRegCode
  refine .seq (T₁ := 53) (T₂ := 55)
    (writeDenseQRegCode_exec hrD_ge hrQ_ge hw hU hx her hd hrD hrQ hq hsz hm2 hm3)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_er, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = writeFieldMem w 0 x.mem (itemQuotBitOff U V w N d) (quotientBits U N) q :=
    congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_meta : ∀ a < epochMetaWords U w N, y1.mem a = x.mem a := by
    intro a ha
    have ha_bits : (a + 1) * w ≤ itemQuotBitOff U V w N d := by
      unfold itemQuotBitOff itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    rw [hy1_mem]
    apply word_eq_of_readBit_eq hw
      (writeFieldMem_fits hw hx.mem_wf.mem_fits hqw q a) (hx.mem_wf.mem_fits a)
    intro j hj
    rw [readBit_writeFieldMem hw _ hqw (a * w + j)]
    have hnot : ¬(itemQuotBitOff U V w N d ≤ a * w + j ∧
        a * w + j < itemQuotBitOff U V w N d + quotientBits U N) := by
      rw [Nat.add_one_mul] at ha_bits; omega
    rw [ite_eq_right hnot]
  have h2_lt : 2 < epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
  have h3_lt : 3 < epochMetaWords U w N := by unfold epochMetaWords; split_ifs <;> omega
  refine (writeDenseVRegCode_frame hrD_ge hrV_ge hw hU hV hy1_wf hy1_er hd
    (by rw [hy1_regs rD hrD_ge, hrD]) (by rw [hy1_regs rV hrV_ge, hrV]) hv
    (by rw [hy1_sz]; exact hsz)
    (by rw [hy1_meta 2 h2_lt, hm2]) (by rw [hy1_meta 3 h3_lt, hm3])).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_v, hy_v_other, hy_q_pres, hy_meta, hy_regs⟩ => ?_) le_rfl
  have hy1_q_self : denseQuotAt U V w N y1.toBitMemoryState d = q := by
    unfold denseQuotAt BitMemory.State.getField
    change readField w 0 y1.mem (itemQuotBitOff U V w N d) (quotientBits U N) = q
    rw [hy1_mem, readField_writeFieldMem_same hw _ hqw hq]
  refine ⟨hy_wf, hy_er, hy_sz.trans hy1_sz, (hy_q_pres d hd).trans hy1_q_self, hy_v,
    fun d' hd' hne => ?_,
    fun a ha => (hy_meta a ha).trans (hy1_meta a ha),
    fun r hr => (hy_regs r hr).trans (hy1_regs r hr)⟩
  have hdisj_item : itemBitOff U V w N d' + itemBits U V N ≤ itemBitOff U V w N d ∨
      itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N d' := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · left
      have : (d' + 1) * itemBits U V N ≤ d * itemBits U V N := Nat.mul_le_mul_right _ hlt
      rw [← itemBitOff_succ]; simp only [itemBitOff]; omega
    · right
      have : (d + 1) * itemBits U V N ≤ d' * itemBits U V N := Nat.mul_le_mul_right _ hgt
      rw [← itemBitOff_succ]; simp only [itemBitOff]; omega
  have hq_disj : itemQuotBitOff U V w N d' + quotientBits U N ≤ itemQuotBitOff U V w N d ∨
      itemQuotBitOff U V w N d + quotientBits U N ≤ itemQuotBitOff U V w N d' := by
    rcases hdisj_item with h1 | h2
    · left; simp only [itemQuotBitOff, itemBits] at h1 ⊢; omega
    · right; simp only [itemQuotBitOff, itemBits] at h2 ⊢; omega
  have hv_disj : itemValBitOff U V w N d' + valBits V ≤ itemQuotBitOff U V w N d ∨
      itemQuotBitOff U V w N d + quotientBits U N ≤ itemValBitOff U V w N d' := by
    rcases hdisj_item with h1 | h2
    · left; simp only [itemValBitOff, itemQuotBitOff, itemBits] at h1 ⊢; omega
    · right; simp only [itemValBitOff, itemQuotBitOff, itemBits] at h2 ⊢; omega
  have hy1_q_other : denseQuotAt U V w N y1.toBitMemoryState d' =
      denseQuotAt U V w N x.toBitMemoryState d' := by
    unfold denseQuotAt BitMemory.State.getField
    change readField w 0 y1.mem _ _ = readField w 0 x.mem _ _
    rw [hy1_mem, readField_writeFieldMem_of_disjoint hw _ hqw hqw hq_disj]
  have hy1_v_other : denseValAt U V w N y1.toBitMemoryState d' =
      denseValAt U V w N x.toBitMemoryState d' := by
    unfold denseValAt BitMemory.State.getField
    change readField w 0 y1.mem _ _ = readField w 0 x.mem _ _
    rw [hy1_mem, readField_writeFieldMem_of_disjoint hw _ hqw hvw hv_disj]
  exact ⟨(hy_q_pres d' hd').trans hy1_q_other, (hy_v_other d' hd' hne).trans hy1_v_other⟩

/-- Copy dense item `(quotient, value)` from index `rSrc` to index `rDst` (`20 ≤ rSrc, rDst`),
using `r18, r19` as temporaries and preserving `r ≥ 20`. -/
@[expose]
def copyDenseItemRegCode (rSrc rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (readDenseQRegCode rSrc 18)
  (.seq (readDenseVRegCode rSrc 19)
        (writeDenseQVRegCode rDst 18 19))

theorem copyDenseItemRegCode_exec {U V w N n_t d_src d_dst : ℕ} {rSrc rDst : Fin 280}
    {x : BitRAM.Data 280}
    (hrSrc_ge : 20 ≤ rSrc.val) (hrDst_ge : 20 ≤ rDst.val)
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsrc : d_src < n_t) (hdst : d_dst < n_t)
    (hrSrc : x.regs rSrc = d_src) (hrDst : x.regs rDst = d_dst)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hm2 : x.mem 2 = itemBits U V N)
    (hm3 : x.mem 3 = epochMetaBits U w N) :
    BitRAM.DemonicExecWithin w (copyDenseItemRegCode rSrc rDst) x
      (fun y =>
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        y.bitSize = x.bitSize ∧
        denseQuotAt U V w N y.toBitMemoryState d_dst =
          denseQuotAt U V w N x.toBitMemoryState d_src ∧
        denseValAt U V w N y.toBitMemoryState d_dst =
          denseValAt U V w N x.toBitMemoryState d_src ∧
        (∀ d' < n_t, d' ≠ d_dst →
          denseQuotAt U V w N y.toBitMemoryState d' =
            denseQuotAt U V w N x.toBitMemoryState d' ∧
          denseValAt U V w N y.toBitMemoryState d' =
            denseValAt U V w N x.toBitMemoryState d') ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a) ∧
        (∀ r : Fin 280, 20 ≤ r.val → y.regs r = x.regs r)) 195 := by
  unfold copyDenseItemRegCode
  refine .seq (T₁ := 42) (T₂ := 152)
    (readDenseQRegCode_exec (by omega) hw hU hx her hsrc hrSrc hsz hm2 hm3)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_18, hy1_regs⟩ => ?_) (by omega)
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_er : EpochRegs U V w N y1 :=
    her.congr_regs (fun r hr1 _ =>
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  refine .seq (T₁ := 44) (T₂ := 108)
    (readDenseVRegCode_exec (by omega) hw hV hy1_wf hy1_er hsrc
      (by rw [hy1_regs rSrc (by omega) (by intro h; have := congrArg Fin.val h; omega), hrSrc])
      (by rw [hy1_sz]; exact hsz) (by rw [hy1_mem, hm2]) (by rw [hy1_mem, hm3]))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_19, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_mem : y2.mem = x.mem := congrArg BitMemory.State.mem hy2_st_x
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_er : EpochRegs U V w N y2 :=
    hy1_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy2_18 : y2.regs 18 = denseQuotAt U V w N x.toBitMemoryState d_src := by
    rw [hy2_regs 18 (by decide) (by decide), hy1_18]
  have hy2_19_x : y2.regs 19 = denseValAt U V w N x.toBitMemoryState d_src := by
    rw [hy2_19, hy1_st]
  have hy2_dst : y2.regs rDst = d_dst := by
    rw [hy2_regs rDst (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs rDst (by omega) (by intro h; have := congrArg Fin.val h; omega), hrDst]
  refine (writeDenseQVRegCode_exec (by omega) (by decide) (by decide)
    hw hU hV hy2_wf hy2_er hdst hy2_dst hy2_18 hy2_19_x
    (denseQuotAt_lt U V w N x.toBitMemoryState d_src)
    (denseValAt_lt U V w N x.toBitMemoryState d_src)
    (by rw [hy2_sz]; exact hsz) (by rw [hy2_mem, hm2]) (by rw [hy2_mem, hm3])).mono
    (fun y ⟨hy_wf, hy_er, hy_sz, hy_q, hy_v, hy_other, hy_meta, hy_regs⟩ => ?_) le_rfl
  refine ⟨hy_wf, hy_er, hy_sz.trans hy2_sz, hy_q, hy_v,
    fun d' hd' hne => ?_,
    fun a ha => (hy_meta a ha).trans (congrFun hy2_mem a),
    fun r hr => ?_⟩
  · obtain ⟨hq', hv'⟩ := hy_other d' hd' hne
    rw [hy2_st_x] at hq' hv'
    exact ⟨hq', hv'⟩
  · rw [hy_regs r (by omega),
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]

/-! ## Section 2: `WindowInv`, circular window updates, and `physByBase` correspondence -/

/-- Circular tail-to-dense bijection invariant on an arbitrary dense interval `[b, b + n)` with
modulus `M`. `TailDenseInv N n_slabs n_tails td dt` is `WindowInv (maxTailItems N)
(n_slabs * slabSize N) n_tails td dt`. -/
structure WindowInv (M b n : ℕ) (td dt : ℕ → ℕ) : Prop where
  td_lt : ∀ t < n, td t < M
  dense_lt : ∀ t < n, denseOfCirc M b (td t) < b + n
  dt_td : ∀ t < n, dt (td t) = t
  owner_valid : ∀ d, b ≤ d → d < b + n → dt (d % M) < n ∧ td (dt (d % M)) = d % M

theorem windowInv_iff_tailDenseInv (N n_slabs n_tails : ℕ) (td dt : ℕ → ℕ) :
    WindowInv (maxTailItems N) (n_slabs * slabSize N) n_tails td dt ↔
      TailDenseInv N n_slabs n_tails td dt :=
  ⟨fun h => ⟨h.td_lt, h.dense_lt, h.dt_td, h.owner_valid⟩,
   fun h => ⟨h.td_lt, h.dense_lt, h.dt_td, h.owner_valid⟩⟩

theorem denseOfCirc_ge (M b c : ℕ) : b ≤ denseOfCirc M b c := by
  unfold denseOfCirc; split_ifs <;> omega

theorem denseOfCirc_eq_self_iff {M b c d : ℕ} (hM : 0 < M) (hc : c < M)
    (hlo : b ≤ d) (hhi : d < b + M) :
    denseOfCirc M b c = d ↔ c = d % M := by
  constructor
  · intro heq
    rw [← heq, denseOfCirc_mod hM hc]
  · rintro rfl
    exact denseOfCirc_mod_self hM hlo hhi

theorem denseOfCirc_succ_of_ne_mod {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M b c < b + M) (hne : c ≠ b % M) :
    denseOfCirc M (b + 1) c = denseOfCirc M b c := by
  set d := denseOfCirc M b c
  have hlo : b ≤ d := denseOfCirc_ge M b c
  have hne_d : d ≠ b := fun hd => hne ((denseOfCirc_eq_self_iff hM hc le_rfl (by omega)).mp hd)
  have hmod : d % M = c := denseOfCirc_mod hM hc
  rw [← hmod]
  exact denseOfCirc_mod_self hM (by omega) (by omega)

theorem denseOfCirc_pred_of_lt {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M (b + 1) c < b + M) :
    denseOfCirc M b c = denseOfCirc M (b + 1) c ∧ c ≠ b % M := by
  set d := denseOfCirc M (b + 1) c
  have hlo : b + 1 ≤ d := denseOfCirc_ge M (b + 1) c
  have hmod : d % M = c := denseOfCirc_mod hM hc
  have heq : denseOfCirc M b c = d := by
    rw [← hmod]
    exact denseOfCirc_mod_self hM (by omega) hhi
  refine ⟨heq, fun hmod_b => ?_⟩
  have hdb : denseOfCirc M b c = b := by
    rw [hmod_b]
    exact denseOfCirc_mod_self hM le_rfl (by omega)
  omega

/-- Canonical `td` mapping `(b + t) % M` for initial / rebuilt companions. -/
@[expose]
def canonTD (M b : ℕ) (t : ℕ) : ℕ :=
  if M = 0 then 0 else (b + t) % M

/-- Canonical `dt` mapping `(c + M - b % M) % M` for initial / rebuilt companions. -/
@[expose]
def canonDT (M b : ℕ) (c : ℕ) : ℕ :=
  if M = 0 then 0 else (c + M - b % M) % M

theorem windowInv_canon {M b n : ℕ} (hn : n ≤ M) :
    WindowInv M b n (canonTD M b) (canonDT M b) ∧
    (∀ i, canonTD M b i < max M 1) ∧
    (∀ i, canonDT M b i < max M 1) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have hn0 : n = 0 := by omega
    subst hn0
    refine ⟨⟨by omega, by omega, by omega, by omega⟩, fun _ => ?_, fun _ => ?_⟩ <;>
    · simp [canonTD, canonDT]
  · have hM0 : M ≠ 0 := Nat.ne_of_gt hM
    have hmax : max M 1 = M := max_eq_left hM
    have htd_eq : ∀ t, canonTD M b t = (b + t) % M := fun t => by simp [canonTD, hM0]
    have hdt_eq : ∀ c, canonDT M b c = (c + M - b % M) % M := fun c => by simp [canonDT, hM0]
    have hcirc : ∀ c, denseOfCirc M b c = b + canonDT M b c := by
      intro c; unfold denseOfCirc; rw [ite_eq_right hM0, hdt_eq]
    refine ⟨⟨fun t _ => by rw [htd_eq]; exact Nat.mod_lt _ hM,
      fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
      fun i => by rw [hmax, htd_eq]; exact Nat.mod_lt _ hM,
      fun i => by rw [hmax, hdt_eq]; exact Nat.mod_lt _ hM⟩
    · rw [htd_eq, denseOfCirc_mod_self hM (by omega) (by omega)]
      omega
    · have h1 : denseOfCirc M b (canonTD M b t) = b + t := by
        rw [htd_eq]; exact denseOfCirc_mod_self hM (by omega) (by omega)
      rw [hcirc] at h1
      omega
    · have h1 : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM hlo (by omega)
      rw [hcirc] at h1
      have hdt_val : canonDT M b (d % M) = d - b := by omega
      rw [hdt_val]
      refine ⟨by omega, ?_⟩
      rw [htd_eq, Nat.add_sub_of_le hlo]

/-- Physical slot of dense item `d` parameterized explicitly by the tail base `b_tail`. -/
@[expose]
def physByBase (N b_tail : ℕ) (dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < b_tail then d
  else N - 1 - dt (d % maxTailItems N)

theorem physOfDense_eq_physByBase (N : ℕ) (gm dt : ℕ → ℕ) :
    physOfDense N gm dt = physByBase N (gm 0 * slabSize N) dt := by
  rfl

/-- Grow the circular window `[b, b + n)` on the right by 1 to `[b, b + (n + 1))`. -/
@[expose]
def winGrowRight (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c := (b + n) % M
  (Function.update p.1 n c, Function.update p.2 c n)

theorem winGrowRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winGrowRight M b n (td, dt)
    WindowInv M b (n + 1) p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_new := (b + n) % M
  have hc_lt : c_new < M := Nat.mod_lt (b + n) hM_pos
  have hcirc_new : denseOfCirc M b c_new = b + n :=
    denseOfCirc_mod_self hM_pos (by omega) (by omega)
  have htd_ne : ∀ t < n, td t ≠ c_new := by
    intro t ht heq
    have := hw.dense_lt t ht
    rw [heq, hcirc_new] at this
    omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (htd_ne t ht')]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · dsimp only [p', winGrowRight]
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show d < b + n + 1 by omega) with hd_lt | rfl
    · have hown := hw.owner_valid d hlo hd_lt
      have hne_c : d % M ≠ c_new := by
        rw [← hown.2]
        exact htd_ne _ hown.1
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
    · rw [Function.update_self, Function.update_self]
      exact ⟨Nat.lt_succ_self n, rfl⟩
  · dsimp only [p', winGrowRight]
    by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · dsimp only [p', winGrowRight]
    by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Grow the circular window `[b + 1, b + 1 + n)` on the left by 1 to `[b, b + (n + 1))`. -/
@[expose]
def winGrowLeft (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c := b % M
  (Function.update p.1 n c, Function.update p.2 c n)

theorem winGrowLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M (b + 1) n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winGrowLeft M b n (td, dt)
    WindowInv M b (n + 1) p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_new := b % M
  have hc_lt : c_new < M := Nat.mod_lt b hM_pos
  have hcirc_new : denseOfCirc M b c_new = b :=
    denseOfCirc_mod_self hM_pos le_rfl (by omega)
  have hpred : ∀ t < n, denseOfCirc M b (td t) = denseOfCirc M (b + 1) (td t) ∧ td t ≠ c_new := by
    intro t ht
    have hlt := hw.dense_lt t ht
    exact denseOfCirc_pred_of_lt hM_pos (hw.td_lt t ht) (by omega)
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht')]; exact hw.td_lt t ht'
    · rw [Function.update_self]; exact hc_lt
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), (hpred t ht').1]
      have := hw.dense_lt t ht'; omega
    · rw [Function.update_self, hcirc_new]; omega
  · dsimp only [p', winGrowLeft]
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl
    · rw [Function.update_of_ne (Nat.ne_of_lt ht'), Function.update_of_ne (hpred t ht').2]
      exact hw.dt_td t ht'
    · rw [Function.update_self, Function.update_self]
  · dsimp only [p', winGrowLeft]
    rcases eq_or_lt_of_le hlo with rfl | hd_gt
    · rw [Function.update_self, Function.update_self]
      exact ⟨Nat.lt_succ_self n, rfl⟩
    · have hown := hw.owner_valid d hd_gt (by omega)
      have hne_c : d % M ≠ c_new := by
        rw [← hown.2]
        exact (hpred _ hown.1).2
      rw [Function.update_of_ne hne_c, Function.update_of_ne (Nat.ne_of_lt hown.1)]
      exact ⟨by omega, hown.2⟩
  · dsimp only [p', winGrowLeft]
    by_cases hi : i = n
    · subst hi; rw [Function.update_self]; exact hc_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · dsimp only [p', winGrowLeft]
    by_cases hi : i = c_new
    · subst hi; rw [Function.update_self]; omega
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Shrink the circular window `[b, b + (n + 1))` on the right by 1 to `[b, b + n)`. -/
@[expose]
def winShrinkRight (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c_rem := (b + n) % M
  let t_rem := p.2 c_rem
  let c_last := p.1 n
  (Function.update p.1 t_rem c_last, Function.update p.2 c_last t_rem)

theorem winShrinkRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winShrinkRight M b n (td, dt)
    WindowInv M b n p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_rem := (b + n) % M
  set t_rem := dt c_rem
  set c_last := td n
  have hown_rem := hw.owner_valid (b + n) (by omega) (by omega)
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hlt_bn : ∀ t < n + 1, t ≠ t_rem → denseOfCirc M b (td t) < b + n := by
    intro t ht hne
    have hlt := hw.dense_lt t ht
    have hne_d : denseOfCirc M b (td t) ≠ b + n := by
      intro hd
      have hmod : td t = c_rem := (denseOfCirc_eq_self_iff hM_pos (hw.td_lt t ht)
        (by omega) (by omega)).mp hd
      exact hne (htd_inj t ht t_rem ht_rem_lt (hmod.trans htd_trem.symm))
    omega
  have hp'1 : p'.1 = Function.update td t_rem c_last := rfl
  have hp'2 : p'.2 = Function.update dt c_last t_rem := rfl
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne heq]; exact hw.td_lt t (by omega)
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]
      exact hlt_bn n (Nat.lt_succ_self n) (by omega)
    · rw [Function.update_of_ne heq]
      exact hlt_bn t (by omega) heq
  · rw [hp'1, hp'2]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq]
      have hne_c : td t ≠ c_last := fun hc =>
         Nat.ne_of_lt ht (htd_inj t (by omega) n (Nat.lt_succ_self n) hc)
      rw [Function.update_of_ne hne_c]
      exact hw.dt_td t (by omega)
  · rw [hp'1, hp'2]
    have hown := hw.owner_valid d hlo (by omega)
    have hne_crem : d % M ≠ c_rem := by
      intro heq
      have hd_eq : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM_pos hlo (by omega)
      have hrem_eq : denseOfCirc M b c_rem = b + n :=
        denseOfCirc_mod_self hM_pos (by omega) (by omega)
      rw [heq, hrem_eq] at hd_eq
      omega
    have hne_trem : dt (d % M) ≠ t_rem := by
      intro heq
      apply hne_crem
      rw [← hown.2, heq, htd_trem]
    by_cases hclast : d % M = c_last
    · rw [hclast, Function.update_self, Function.update_self]
      have hne_n : t_rem ≠ n := by
        intro heq
        apply hne_crem
        rw [hclast, ← htd_trem, heq]
      exact ⟨by omega, rfl⟩
    · rw [Function.update_of_ne hclast, Function.update_of_ne hne_trem]
      have hne_n : dt (d % M) ≠ n := by
        intro heq
        apply hclast
        rw [← hown.2, heq]
      exact ⟨by omega, hown.2⟩
  · rw [hp'1]
    by_cases hi : i = t_rem
    · subst hi; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · rw [hp'2]
    by_cases hi : i = c_last
    · subst hi; rw [Function.update_self]; exact hdt_b c_rem
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Shrink the circular window `[b, b + (n + 1))` on the left by 1 to `[b + 1, b + 1 + n)`. -/
@[expose]
def winShrinkLeft (M b n : ℕ) (p : (ℕ → ℕ) × (ℕ → ℕ)) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let c_rem := b % M
  let t_rem := p.2 c_rem
  let c_last := p.1 n
  (Function.update p.1 t_rem c_last, Function.update p.2 c_last t_rem)

theorem winShrinkLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    let p' := winShrinkLeft M b n (td, dt)
    WindowInv M (b + 1) n p'.1 p'.2 ∧
    (∀ i, p'.1 i < M) ∧ (∀ i, p'.2 i < M) := by
  intro p'
  have hM_pos : 0 < M := by omega
  set c_rem := b % M
  set t_rem := dt c_rem
  set c_last := td n
  have hown_rem := hw.owner_valid b le_rfl (by omega)
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  have htd_inj : ∀ t₁ < n + 1, ∀ t₂ < n + 1, td t₁ = td t₂ → t₁ = t₂ := by
    intro t₁ ht₁ t₂ ht₂ heq
    rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]
  have hsucc : ∀ t < n + 1, t ≠ t_rem →
      denseOfCirc M (b + 1) (td t) < b + 1 + n := by
    intro t ht hne
    have hlt := hw.dense_lt t ht
    have hne_c : td t ≠ c_rem := fun hc =>
      hne (htd_inj t ht t_rem ht_rem_lt (hc.trans htd_trem.symm))
    rw [denseOfCirc_succ_of_ne_mod hM_pos (hw.td_lt t ht) (by omega) hne_c]
    omega
  have hp'1 : p'.1 = Function.update td t_rem c_last := rfl
  have hp'2 : p'.2 = Function.update dt c_last t_rem := rfl
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne heq]; exact hw.td_lt t (by omega)
  · rw [hp'1]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self]
      exact hsucc n (Nat.lt_succ_self n) (by omega)
    · rw [Function.update_of_ne heq]
      exact hsucc t (by omega) heq
  · rw [hp'1, hp'2]
    by_cases heq : t = t_rem
    · subst heq; rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heq]
      have hne_c : td t ≠ c_last := fun hc =>
        Nat.ne_of_lt ht (htd_inj t (by omega) n (Nat.lt_succ_self n) hc)
      rw [Function.update_of_ne hne_c]
      exact hw.dt_td t (by omega)
  · rw [hp'1, hp'2]
    have hown := hw.owner_valid d (by omega) (by omega)
    have hne_crem : d % M ≠ c_rem := by
      intro heq
      have hd_eq : denseOfCirc M b (d % M) = d :=
        denseOfCirc_mod_self hM_pos (by omega) (by omega)
      have hrem_eq : denseOfCirc M b c_rem = b :=
        denseOfCirc_mod_self hM_pos le_rfl (by omega)
      rw [heq, hrem_eq] at hd_eq
      omega
    have hne_trem : dt (d % M) ≠ t_rem := by
      intro heq
      apply hne_crem
      rw [← hown.2, heq, htd_trem]
    by_cases hclast : d % M = c_last
    · rw [hclast, Function.update_self, Function.update_self]
      have hne_n : t_rem ≠ n := by
        intro heq
        apply hne_crem
        rw [hclast, ← htd_trem, heq]
      exact ⟨by omega, rfl⟩
    · rw [Function.update_of_ne hclast, Function.update_of_ne hne_trem]
      have hne_n : dt (d % M) ≠ n := by
        intro heq
        apply hclast
        rw [← hown.2, heq]
      exact ⟨by omega, hown.2⟩
  · rw [hp'1]
    by_cases hi : i = t_rem
    · subst hi; rw [Function.update_self]; exact hc_last_lt
    · rw [Function.update_of_ne hi]; exact htd_b i
  · rw [hp'2]
    by_cases hi : i = c_last
    · subst hi; rw [Function.update_self]; exact hdt_b c_rem
    · rw [Function.update_of_ne hi]; exact hdt_b i

/-- Effect of `winGrowRight` on `physByBase`: preserves `physByBase` for all `d < b + n` and maps
`b + n` to `N - 1 - n`. -/
theorem physByBase_winGrowRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    let dt' := (winGrowRight (maxTailItems N) b n (td, dt)).2
    physByBase N b dt' (b + n) = N - 1 - n ∧
    (∀ d < b + n, physByBase N b dt' d = physByBase N b dt d) := by
  intro dt'
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd => ?_⟩
  · unfold physByBase
    rw [ite_eq_right hb0, ite_eq_right (by omega)]
    dsimp only [dt', winGrowRight]
    rw [Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    split_ifs with hlt
    · rfl
    · have hlo : b ≤ d := Nat.le_of_not_lt hlt
      have hne : d % maxTailItems N ≠ (b + n) % maxTailItems N := by
        intro heq
        have h1 := denseOfCirc_mod_self hM_pos hlo (by omega : d < b + maxTailItems N)
        have h2 := denseOfCirc_mod_self (base_tail := b) (d := b + n) hM_pos
          (by omega) (by omega)
        rw [heq, h2] at h1
        omega
      dsimp only [dt', winGrowRight]
      rw [Function.update_of_ne hne]

/-- Effect of `winGrowLeft` on `physByBase`: maps `b` to `N - 1 - n` and preserves `physByBase`
for all `d < b + 1 + n` with `d ≠ b`. -/
theorem physByBase_winGrowLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    let dt' := (winGrowLeft (maxTailItems N) b n (td, dt)).2
    physByBase N b dt' b = N - 1 - n ∧
    (∀ d < b + 1 + n, d ≠ b → physByBase N b dt' d = physByBase N (b + 1) dt d) := by
  intro dt'
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd hne => ?_⟩
  · unfold physByBase
    rw [ite_eq_right hb0, ite_eq_right (by omega)]
    dsimp only [dt', winGrowLeft]
    rw [Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    by_cases hlt : d < b
    · have hlt1 : d < b + 1 := by omega
      simp only [hlt, hlt1, ↓reduceIte]
    · have hgt : ¬d < b + 1 := by omega
      simp only [hlt, hgt, ↓reduceIte]
      have hlo : b ≤ d := by omega
      have hne_mod : d % maxTailItems N ≠ b % maxTailItems N := by
        intro heq
        have h1 := denseOfCirc_mod_self hM_pos hlo (by omega : d < b + maxTailItems N)
        have h2 := denseOfCirc_mod_self (base_tail := b) (d := b) hM_pos
          le_rfl (by omega : b < b + maxTailItems N)
        rw [heq, h2] at h1
        exact hne h1.symm
      dsimp only [dt', winGrowLeft]
      rw [Function.update_of_ne hne_mod]

/-- Effect of `winShrinkRight` on `physByBase`: maps `denseOfCirc M b (td n)` to
`physByBase N b dt (b + n)` and preserves `physByBase` for all `d < b + n` with
`d ≠ denseOfCirc M b (td n)`. -/
theorem physByBase_winShrinkRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    let M := maxTailItems N
    let dt' := (winShrinkRight M b n (td, dt)).2
    let d_last := denseOfCirc M b (td n)
    d_last < b + n + 1 ∧
    physByBase N b dt' d_last = physByBase N b dt (b + n) ∧
    (∀ d < b + n, d ≠ d_last → physByBase N b dt' d = physByBase N b dt d) := by
  intro M dt' d_last
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < M := by omega
  have hd_last_lt : d_last < b + n + 1 := hw.dense_lt n (Nat.lt_succ_self n)
  have hd_last_ge : b ≤ d_last := denseOfCirc_ge M b (td n)
  have hc_last_lt : td n < M := hw.td_lt n (Nat.lt_succ_self n)
  have hd_last_mod : d_last % M = td n := denseOfCirc_mod hM_pos hc_last_lt
  refine ⟨hd_last_lt, ?_, fun d hd hne => ?_⟩
  · have hnot1 : ¬d_last < b := by omega
    have hnot2 : ¬(b + n) < b := by omega
    simp only [physByBase, hb0, hnot1, hnot2, ↓reduceIte]
    change N - 1 - dt' (d_last % M) = N - 1 - dt ((b + n) % M)
    rw [hd_last_mod]
    dsimp only [dt', winShrinkRight]
    rw [Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    split_ifs with hlt
    · rfl
    · have hlo : b ≤ d := Nat.le_of_not_lt hlt
      have hne_mod : d % M ≠ td n := by
        intro heq
        apply hne
        rw [← (denseOfCirc_eq_self_iff hM_pos hc_last_lt hlo (by omega : d < b + M)).mpr heq.symm]
      change N - 1 - dt' (d % M) = N - 1 - dt (d % M)
      dsimp only [dt', winShrinkRight]
      rw [Function.update_of_ne hne_mod]

/-- Effect of `winShrinkLeft` on `physByBase`: maps `denseOfCirc M b (td n)` (when `> b`) to
`N - 1 - dt (b % M)` and preserves `physByBase` for all `d` with `b + 1 ≤ d < b + 1 + n` and
`d ≠ denseOfCirc M b (td n)`. -/
theorem physByBase_winShrinkLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    let M := maxTailItems N
    let dt' := (winShrinkLeft M b n (td, dt)).2
    let d_last := denseOfCirc M b (td n)
    b ≤ d_last ∧ d_last < b + n + 1 ∧
    (b < d_last → physByBase N (b + 1) dt' d_last = N - 1 - dt (b % M)) ∧
    (∀ d < b + 1 + n, d ≠ b → d ≠ d_last →
      physByBase N (b + 1) dt' d = physByBase N b dt d) := by
  intro M dt' d_last
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < M := by omega
  have hd_last_lt : d_last < b + n + 1 := hw.dense_lt n (Nat.lt_succ_self n)
  have hd_last_ge : b ≤ d_last := denseOfCirc_ge M b (td n)
  have hc_last_lt : td n < M := hw.td_lt n (Nat.lt_succ_self n)
  have hd_last_mod : d_last % M = td n := denseOfCirc_mod hM_pos hc_last_lt
  refine ⟨hd_last_ge, hd_last_lt, fun hgt => ?_, fun d hd hneb hne => ?_⟩
  · have hnot : ¬d_last < b + 1 := by omega
    simp only [physByBase, hb0, hnot, ↓reduceIte]
    change N - 1 - dt' (d_last % M) = N - 1 - dt (b % M)
    rw [hd_last_mod]
    dsimp only [dt', winShrinkLeft]
    rw [Function.update_self]
  · simp only [physByBase, hb0, ↓reduceIte]
    by_cases hlt : d < b
    · have hlt1 : d < b + 1 := by omega
      simp only [hlt, hlt1, ↓reduceIte]
    · have hnot1 : ¬d < b + 1 := by omega
      simp only [hlt, hnot1, ↓reduceIte]
      have hd_ge_b : b ≤ d := by omega
      have hne_mod : d % M ≠ td n := by
        intro heq
        apply hne
        rw [← (denseOfCirc_eq_self_iff hM_pos hc_last_lt hd_ge_b (by omega : d < b + M)).mpr
          heq.symm]
      change N - 1 - dt' (d % M) = N - 1 - dt (d % M)
      dsimp only [dt', winShrinkLeft]
      rw [Function.update_of_ne hne_mod]

/-! ## Section 3: `WindowCoupled` and `FixedCoupled` coupling predicates -/

/-- Coupling invariant between a fixed-capacity state `s_fix : Memory.State` (at `base = 0`,
`h_space = Succinct.hashSpace U w N`) and a bit-resizable state `s_bit : BitMemory.State` over an
active circular tail window `[b_win, b_win + n_win)` and `m_items` dense items. -/
structure WindowCoupled (U V w N b_win n_win m_items : ℕ)
    (s_fix : Memory.State) (s_bit : BitMemory.State) : Prop where
  gm_eq : gmAtBit U w N s_bit.mem =
    Succinct.gmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
  lm_eq : lmAtBit U w N s_bit.mem =
    Succinct.lmAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
  win_inv : WindowInv (maxTailItems N) b_win n_win
    (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem)
  td_lt : ∀ i, tdAtBit U w N s_bit.mem i < max (maxTailItems N) 1
  dt_lt : ∀ i, dtAtBit U w N s_bit.mem i < max (maxTailItems N) 1
  quot_eq : ∀ d < m_items,
    denseQuotAt U V w N s_bit d =
      Succinct.quotAt 0 U w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N s_bit.mem) d)
  val_eq : ∀ d < m_items,
    denseValAt U V w N s_bit d =
      Succinct.valAt 0 U V w N (Succinct.hashSpace U w N) s_fix.mem
        (physByBase N b_win (dtAtBit U w N s_bit.mem) d)

/-- Full coupling invariant when the circular tail window is aligned with `gm 0 * slabSize N` and
`gm 1` (`b_win = gm 0 * slabSize N`, `n_win = gm 1`, `m_items = totalSlots N gm`). -/
@[expose]
def FixedCoupled (U V w N : ℕ) (s_fix : Memory.State) (s_bit : BitMemory.State) : Prop :=
  WindowCoupled U V w N
    (gmAtBit U w N s_bit.mem 0 * slabSize N)
    (gmAtBit U w N s_bit.mem 1)
    (Succinct.totalSlots N (gmAtBit U w N s_bit.mem))
    s_fix s_bit

/-- Any `s_bit` satisfying `FixedCoupled U V w N s_fix s_bit` for a fixed-capacity state `s_fix`
satisfying `Succinct.BucketStateInv` automatically satisfies `BucketRepInv`. -/
theorem bucketRepInv_of_fixedCoupled {U V w N : ℕ} {mOf : ℕ → ℕ}
    {L : ℕ → ℕ → List ℕ} {B : ℕ → ℕ → Option ℕ}
    {s_fix : Memory.State} {s_bit : BitMemory.State}
    (hfix : Succinct.BucketStateInv U V w N (Succinct.hashSpace U w N) 0 mOf L B s_fix)
    (hcpl : FixedCoupled U V w N s_fix s_bit) :
    BucketRepInv U V w N mOf L B s_bit := by
  have htd : TailDenseInv N (gmAtBit U w N s_bit.mem 0) (gmAtBit U w N s_bit.mem 1)
      (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem) :=
    (windowInv_iff_tailDenseInv N _ _ _ _).mp hcpl.win_inv
  exact bucketRepInv_of_fixed hfix hcpl.gm_eq hcpl.lm_eq htd hcpl.quot_eq hcpl.val_eq

/-! ## Section 4: Uniform `BitRAM` programs for circular window operations -/

theorem two_mul_maxTailItems_le_globalMetaLen {N : ℕ} (hb_pos : 0 < bucketBits N) :
    2 * maxTailItems N ≤ globalMetaLen N := by
  unfold globalMetaLen globalMetaVarLen maxTailItems
  rw [ite_eq_right (Nat.ne_of_gt hb_pos)]
  have h2M : 2 * (numBuckets N * tailCapPerBucket N) ≤
      numBuckets N * (3 + dirSlabsPerBucket N + 2 * tailCapPerBucket N) := by
    calc 2 * (numBuckets N * tailCapPerBucket N)
        = numBuckets N * (2 * tailCapPerBucket N) := by ring
      _ ≤ numBuckets N * (3 + dirSlabsPerBucket N + 2 * tailCapPerBucket N) :=
          Nat.mul_le_mul_left _ (by omega)
  omega

/-- Compute `denseOfCirc (maxTailItems N) b_win c` into `rDst` given `rB = b_win` and `rC = c`,
using `r12, r13` as scratch and preserving `r ≥ 14` (`r ≠ rDst`). -/
@[expose]
def denseOfTailRegCode (rB rC rDst : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mod 12 rB 253))
  (.seq (.op (.bin .add 13 rC 253))
  (.seq (.op (.bin .sub 13 13 12))
  (.seq (.op (.bin .mod 13 13 253))
        (.op (.bin .add rDst rB 13)))))

theorem denseOfTailRegCode_exec {U V w N b_win c : ℕ} {rB rC rDst : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 14 ≤ rB.val) (hrC_ge : 14 ≤ rC.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hd_le : denseOfCirc (maxTailItems N) b_win c ≤ N) (hc_lt : c < maxTailItems N)
    (hrB : x.regs rB = b_win) (hrC : x.regs rC = c) :
    BitRAM.DemonicExecWithin w (denseOfTailRegCode rB rC rDst) x
      (fun y =>
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.regs rDst = denseOfCirc (maxTailItems N) b_win c ∧
        (∀ r : Fin 280, 14 ≤ r.val → r ≠ rDst → y.regs r = x.regs r)) 5 := by
  have h253 : x.regs 253 = maxTailItems N := (her.active hN_pos).2.2.2.2.2.2.2.2.1
  set M := maxTailItems N
  have hM_pos : 0 < M := by omega
  have hM_ne : M ≠ 0 := Nat.ne_of_gt hM_pos
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have h2M_le : 2 * M ≤ globalMetaLen N := two_mul_maxTailItems_le_globalMetaLen hb_pos
  have hmod1_lt : b_win % M < M := Nat.mod_lt _ hM_pos
  have hfit_mod1 : Fits w (b_win % M) := hfit_gm _ (by omega)
  have hfit_add1 : Fits w (c + M) := hfit_gm _ (by omega)
  have hfit_sub1 : Fits w (c + M - b_win % M) := hfit_gm _ (by omega)
  have hmod2_lt : (c + M - b_win % M) % M < M := Nat.mod_lt _ hM_pos
  have hfit_mod2 : Fits w ((c + M - b_win % M) % M) := hfit_gm _ (by omega)
  have hdense_eq : b_win + (c + M - b_win % M) % M = denseOfCirc M b_win c := by
    unfold denseOfCirc; rw [ite_eq_right hM_ne]
  have hfit_res : Fits w (b_win + (c + M - b_win % M) % M) := by
    rw [hdense_eq]
    exact fits_of_le_N hw hnU hU (by omega)
  have hneB12 : rB ≠ 12 := by intro h; subst h; omega
  have hneB13 : rB ≠ 13 := by intro h; subst h; omega
  have hneC12 : rC ≠ 12 := by intro h; subst h; omega
  unfold denseOfTailRegCode
  refine step_dExec_bin (v := b_win % M) (T := 4)
    (by simp [BinOp.eval, hrB, h253, M]) hfit_mod1 ?_
  refine step_dExec_bin (v := c + M) (T := 3)
    (by simp [BitRAM.Data.set, hneC12, BinOp.eval, hrC, h253, M]) hfit_add1 ?_
  refine step_dExec_bin (v := c + M - b_win % M) (T := 2)
    (by simp +decide [BitRAM.Data.set, BinOp.eval]) hfit_sub1 ?_
  refine step_dExec_bin (v := (c + M - b_win % M) % M) (T := 1)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, h253, M]) hfit_mod2 ?_
  refine dExec_bin (v := b_win + (c + M - b_win % M) % M)
    (by simp [BitRAM.Data.set, hneB12, hneB13, BinOp.eval, hrB]) hfit_res ?_
  refine ⟨rfl,
    wf_set rDst (wf_set 13 (wf_set 13 (wf_set 13 (wf_set 12 hx hfit_mod1) hfit_add1) hfit_sub1)
      hfit_mod2) hfit_res,
    ?_, fun r hr hne => ?_⟩
  · simp only [BitRAM.Data.set, Function.update_self, denseOfCirc, M, ite_eq_right hM_ne]
  · dsimp only [BitRAM.Data.set]
    rw [Function.update_of_ne hne]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Uniform `BitRAM.Code .standard 280` program executing
`winGrowRight (maxTailItems N) b_win n_win` on `(tdAtBit, dtAtBit)` given `rB = b_win` and
`rN = n_win` (`18 ≤ rB, rN`). -/
@[expose]
def winGrowRightRegCode (rB rN : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .add 16 rB rN))
  (.seq (.op (.bin .mod 16 16 253))
  (.seq (.op (.copy 17 rN))
  (.seq (writeTDRegCode 17 16)
        (writeDTRegCode 16 17))))

theorem winGrowRightRegCode_exec {U V w N b_win n_win : ℕ} {rB rN : Fin 280}
    {x : BitRAM.Data 280}
    (_hrB_ge : 18 ≤ rB.val) (hrN_ge : 18 ≤ rN.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (hbn_le : b_win + n_win ≤ N) (hM : n_win + 1 ≤ maxTailItems N)
    (hrB : x.regs rB = b_win) (hrN : x.regs rN = n_win) :
    let p' := winGrowRight (maxTailItems N) b_win n_win
      (tdAtBit U w N x.mem, dtAtBit U w N x.mem)
    BitRAM.DemonicExecWithin w (winGrowRightRegCode rB rN) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        tdAtBit U w N y.mem = p'.1 ∧
        dtAtBit U w N y.mem = p'.2 ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        (∀ a < offTD U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 115 := by
  intro p'
  have h253 : x.regs 253 = maxTailItems N := (her.active hN_pos).2.2.2.2.2.2.2.2.1
  set M := maxTailItems N
  have hM_pos : 0 < M := by omega
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have h2M_le : 2 * M ≤ globalMetaLen N := two_mul_maxTailItems_le_globalMetaLen hb_pos
  set c := (b_win + n_win) % M
  have hc_lt : c < M := Nat.mod_lt _ hM_pos
  have hn_lt : n_win < M := by omega
  have hfit_add : Fits w (b_win + n_win) := fits_of_le_N hw hnU hU (by omega)
  have hfit_c : Fits w c := hfit_gm _ (by omega)
  have hfit_n : Fits w n_win := hfit_gm _ (by omega)
  have hneN16 : rN ≠ 16 := by intro h; subst h; omega
  have hc_val : c < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hc_lt (maxTailItems_le N)))
  have hn_val : n_win < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hn_lt (maxTailItems_le N)))
  unfold winGrowRightRegCode
  refine step_dExec_bin (v := b_win + n_win) (T := 114)
    (by simp [BinOp.eval, hrB, hrN]) hfit_add ?_
  refine step_dExec_bin (v := c) (T := 113)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, h253, c, M]) hfit_c ?_
  refine step_dExec_copy (v := n_win) (T := 112)
    (by simp [BitRAM.Data.set, hneN16, hrN]) ?_
  set s1 := ((x.set 16 (b_win + n_win)).set 16 c).set 17 n_win
  have hs1_wf : s1.WellFormed w :=
    wf_set 17 (wf_set 16 (wf_set 16 hx hfit_add) hfit_c) hfit_n
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 56) (T₂ := 56)
    (writeTDRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hs1_wf hs1_er
      hn_lt hc_val (by simp +decide [s1, BitRAM.Data.set])
      (by simp +decide [s1, BitRAM.Data.set]) hsz)
    (fun y1 ⟨hy1_sz, hy1_wf, hy1_er, hy1_td, hy1_gm, hy1_lm, hy1_dt, hy1_out, hy1_items,
      hy1_regs⟩ => ?_) (by omega)
  refine (writeDTRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy1_wf hy1_er
    hc_lt hn_val
    (by rw [hy1_regs 16 (by decide)]; simp +decide [s1, BitRAM.Data.set])
    (by rw [hy1_regs 17 (by decide)]; simp +decide [s1, BitRAM.Data.set])
    (by rw [hy1_sz]; exact hsz)).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_dt, hy_gm, hy_lm, hy_td, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz.trans hy1_sz, hy_wf, hy_er,
    hy_td.trans hy1_td,
    hy_dt.trans (by rw [hy1_dt]; rfl),
    hy_gm.trans hy1_gm,
    hy_lm.trans hy1_lm,
    fun a ha => (hy_out a (Or.inl (by unfold offDT; omega))).trans (hy1_out a (Or.inl ha)),
    fun d => ⟨(hy_items d).1.trans (hy1_items d).1, (hy_items d).2.trans (hy1_items d).2⟩,
    fun r hr => ?_⟩
  rw [hy_regs r (by omega), hy1_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Uniform `BitRAM.Code .standard 280` program executing
`winGrowLeft (maxTailItems N) b_win n_win` on `(tdAtBit, dtAtBit)` given `rB = b_win` and
`rN = n_win` (`18 ≤ rB, rN`). -/
@[expose]
def winGrowLeftRegCode (rB rN : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .mod 16 rB 253))
  (.seq (.op (.copy 17 rN))
  (.seq (writeTDRegCode 17 16)
        (writeDTRegCode 16 17)))

theorem winGrowLeftRegCode_exec {U V w N b_win n_win : ℕ} {rB rN : Fin 280}
    {x : BitRAM.Data 280}
    (_hrB_ge : 18 ≤ rB.val) (hrN_ge : 18 ≤ rN.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hsz : epochMetaBits U w N ≤ x.bitSize)
    (_hb_le : b_win ≤ N) (hM : n_win + 1 ≤ maxTailItems N)
    (hrB : x.regs rB = b_win) (hrN : x.regs rN = n_win) :
    let p' := winGrowLeft (maxTailItems N) b_win n_win
      (tdAtBit U w N x.mem, dtAtBit U w N x.mem)
    BitRAM.DemonicExecWithin w (winGrowLeftRegCode rB rN) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        tdAtBit U w N y.mem = p'.1 ∧
        dtAtBit U w N y.mem = p'.2 ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        (∀ a < offTD U w N, y.mem a = x.mem a) ∧
        (∀ d, denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ r : Fin 280, 18 ≤ r.val → y.regs r = x.regs r)) 114 := by
  intro p'
  have h253 : x.regs 253 = maxTailItems N := (her.active hN_pos).2.2.2.2.2.2.2.2.1
  set M := maxTailItems N
  have hM_pos : 0 < M := by omega
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz hv
  have h2M_le : 2 * M ≤ globalMetaLen N := two_mul_maxTailItems_le_globalMetaLen hb_pos
  set c := b_win % M
  have hc_lt : c < M := Nat.mod_lt _ hM_pos
  have hn_lt : n_win < M := by omega
  have hfit_c : Fits w c := hfit_gm _ (by omega)
  have hfit_n : Fits w n_win := hfit_gm _ (by omega)
  have hneN16 : rN ≠ 16 := by intro h; subst h; omega
  have hc_val : c < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hc_lt (maxTailItems_le N)))
  have hn_val : n_win < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hn_lt (maxTailItems_le N)))
  unfold winGrowLeftRegCode
  refine step_dExec_bin (v := c) (T := 113)
    (by simp [BinOp.eval, hrB, h253, c, M]) hfit_c ?_
  refine step_dExec_copy (v := n_win) (T := 112)
    (by simp [BitRAM.Data.set, hneN16, hrN]) ?_
  set s1 := (x.set 16 c).set 17 n_win
  have hs1_wf : s1.WellFormed w := wf_set 17 (wf_set 16 hx hfit_c) hfit_n
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 56) (T₂ := 56)
    (writeTDRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hs1_wf hs1_er
      hn_lt hc_val (by simp +decide [s1, BitRAM.Data.set])
      (by simp +decide [s1, BitRAM.Data.set]) hsz)
    (fun y1 ⟨hy1_sz, hy1_wf, hy1_er, hy1_td, hy1_gm, hy1_lm, hy1_dt, hy1_out, hy1_items,
      hy1_regs⟩ => ?_) (by omega)
  refine (writeDTRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy1_wf hy1_er
    hc_lt hn_val
    (by rw [hy1_regs 16 (by decide)]; simp +decide [s1, BitRAM.Data.set])
    (by rw [hy1_regs 17 (by decide)]; simp +decide [s1, BitRAM.Data.set])
    (by rw [hy1_sz]; exact hsz)).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_dt, hy_gm, hy_lm, hy_td, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz.trans hy1_sz, hy_wf, hy_er,
    hy_td.trans hy1_td,
    hy_dt.trans (by rw [hy1_dt]; rfl),
    hy_gm.trans hy1_gm,
    hy_lm.trans hy1_lm,
    fun a ha => (hy_out a (Or.inl (by unfold offDT; omega))).trans (hy1_out a (Or.inl ha)),
    fun d => ⟨(hy_items d).1.trans (hy1_items d).1, (hy_items d).2.trans (hy1_items d).2⟩,
    fun r hr => ?_⟩
  rw [hy_regs r (by omega), hy1_regs r (by omega)]
  dsimp only [s1, BitRAM.Data.set]
  repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]

/-- Uniform `BitRAM.Code .standard 280` program executing
`winShrinkRight (maxTailItems N) b_win n_win` on `(tdAtBit, dtAtBit)` and copying dense item
`b_win + n_win` into `denseOfCirc (maxTailItems N) b_win (tdAtBit n_win)`, given `rB = b_win` and
`rN = n_win` (`24 ≤ rB, rN`). -/
@[expose]
def winShrinkRightRegCode (rB rN : Fin 280) : BitRAM.Code .standard 280 :=
  .seq (.op (.bin .add 20 rB rN))
  (.seq (.op (.bin .mod 21 20 253))
  (.seq (readDTRegCode 21 22)
  (.seq (readTDRegCode rN 21)
  (.seq (denseOfTailRegCode rB 21 23)
  (.seq (copyDenseItemRegCode 20 23)
  (.seq (writeTDRegCode 22 21)
        (writeDTRegCode 21 22)))))))

theorem winShrinkRightRegCode_exec {U V w N n_t b_win n_win : ℕ} {rB rN : Fin 280}
    {x : BitRAM.Data 280}
    (hrB_ge : 24 ≤ rB.val) (hrN_ge : 24 ≤ rN.val)
    (hw : 0 < w) (hN_pos : 0 < N) (hnU : N ≤ U) (hU : U < 2 ^ w) (hV : V ≤ 2 ^ w)
    (hb_pos : 0 < bucketBits N)
    (hx : x.WellFormed w) (her : EpochRegs U V w N x)
    (hm2 : x.mem 2 = itemBits U V N) (hm3 : x.mem 3 = epochMetaBits U w N)
    (hsz : itemBitOff U V w N n_t ≤ x.bitSize)
    (hbn_le : b_win + n_win ≤ N) (hM : n_win + 1 ≤ maxTailItems N)
    (hnt : b_win + n_win + 1 ≤ n_t)
    (hwin : WindowInv (maxTailItems N) b_win (n_win + 1)
      (tdAtBit U w N x.mem) (dtAtBit U w N x.mem))
    (hrB : x.regs rB = b_win) (hrN : x.regs rN = n_win) :
    let M := maxTailItems N
    let td := tdAtBit U w N x.mem
    let dt := dtAtBit U w N x.mem
    let p' := winShrinkRight M b_win n_win (td, dt)
    BitRAM.DemonicExecWithin w (winShrinkRightRegCode rB rN) x
      (fun y =>
        y.bitSize = x.bitSize ∧
        y.WellFormed w ∧
        EpochRegs U V w N y ∧
        tdAtBit U w N y.mem = p'.1 ∧
        dtAtBit U w N y.mem = p'.2 ∧
        gmAtBit U w N y.mem = gmAtBit U w N x.mem ∧
        lmAtBit U w N y.mem = lmAtBit U w N x.mem ∧
        (∀ a < offTD U w N, y.mem a = x.mem a) ∧
        (∀ d < b_win + n_win,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState
              (if d = denseOfCirc M b_win (td n_win) then b_win + n_win else d) ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState
              (if d = denseOfCirc M b_win (td n_win) then b_win + n_win else d)) ∧
        (∀ r : Fin 280, 24 ≤ r.val → y.regs r = x.regs r)) 404 := by
  intro M td dt p'
  have h253 : x.regs 253 = maxTailItems N := (her.active hN_pos).2.2.2.2.2.2.2.2.1
  have hM_pos : 0 < M := by omega
  have hsz_meta : epochMetaBits U w N ≤ x.bitSize :=
    (Nat.le_add_right (epochMetaBits U w N) _).trans hsz
  have hfit_gm : ∀ v ≤ globalMetaLen N, Fits w v :=
    fun v hv => fits_of_le_globalMetaLen_of_bitSize hw hN_pos hx hsz_meta hv
  have h2M_le : 2 * M ≤ globalMetaLen N := two_mul_maxTailItems_le_globalMetaLen hb_pos
  set c_rem := (b_win + n_win) % M
  set t_rem := dt c_rem
  set c_last := td n_win
  set d_last := denseOfCirc M b_win c_last
  have hc_rem_lt : c_rem < M := Nat.mod_lt _ hM_pos
  have hn_lt : n_win < M := by omega
  have ht_rem_lt : t_rem < M :=
    lt_of_lt_of_le (hwin.owner_valid (b_win + n_win) (by omega) (by omega)).1 hM
  have hc_last_lt : c_last < M := hwin.td_lt n_win (Nat.lt_succ_self n_win)
  have hd_last_lt_win : d_last < b_win + n_win + 1 :=
    hwin.dense_lt n_win (Nat.lt_succ_self n_win)
  have hd_last_lt : d_last < n_t := lt_of_lt_of_le hd_last_lt_win hnt
  have hd_last_le_N : d_last ≤ N := by omega
  have hfit_add : Fits w (b_win + n_win) := fits_of_le_N hw hnU hU (by omega)
  have hfit_crem : Fits w c_rem := hfit_gm _ (by omega)
  have hclast_val : c_last < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le hc_last_lt (maxTailItems_le N)))
  have htrem_val : t_rem < 2 ^ globalPtrBits N :=
    Succinct.lt_two_pow_globalPtrBits_of_le_n_max
      (le_of_lt (lt_of_lt_of_le ht_rem_lt (maxTailItems_le N)))
  unfold winShrinkRightRegCode
  refine step_dExec_bin (v := b_win + n_win) (T := 403)
    (by simp [BinOp.eval, hrB, hrN]) hfit_add ?_
  refine step_dExec_bin (v := c_rem) (T := 402)
    (by simp +decide [BitRAM.Data.set, BinOp.eval, h253, c_rem, M]) hfit_crem ?_
  set s1 := (x.set 20 (b_win + n_win)).set 21 c_rem
  have hs1_wf : s1.WellFormed w := wf_set 21 (wf_set 20 hx hfit_add) hfit_crem
  have hs1_er : EpochRegs U V w N s1 :=
    her.congr_regs (fun r hr1 _ => by
      dsimp only [s1, BitRAM.Data.set]
      repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)])
  refine .seq (T₁ := 45) (T₂ := 357)
    (readDTRegCode_exec (by decide) hw hN_pos hnU hU hs1_wf hs1_er hc_rem_lt
      (by simp +decide [s1, BitRAM.Data.set]) hsz_meta)
    (fun y1 ⟨hy1_st, hy1_wf, hy1_22, hy1_regs⟩ => ?_) (by omega)
  have hy1_er : EpochRegs U V w N y1 :=
    hs1_er.congr_regs (fun r hr1 _ =>
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy1_rN : y1.regs rN = n_win := by
    rw [hy1_regs rN (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrN
  have hy1_sz : y1.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy1_st
  have hy1_mem : y1.mem = x.mem := congrArg BitMemory.State.mem hy1_st
  refine .seq (T₁ := 45) (T₂ := 312)
    (readTDRegCode_exec (by omega) hw hN_pos hnU hU hy1_wf hy1_er hn_lt hy1_rN
      (by rw [hy1_sz]; exact hsz_meta))
    (fun y2 ⟨hy2_st, hy2_wf, hy2_21, hy2_regs⟩ => ?_) (by omega)
  have hy2_st_x : y2.toBitMemoryState = x.toBitMemoryState := hy2_st.trans hy1_st
  have hy2_sz : y2.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy2_st_x
  have hy2_er : EpochRegs U V w N y2 :=
    hy1_er.congr_regs (fun r hr1 _ =>
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy2_rB : y2.regs rB = b_win := by
    rw [hy2_regs rB (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs rB (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]
    exact hrB
  have hy2_21_eq : y2.regs 21 = c_last := by
    rw [hy2_21, hy1_mem]
  refine .seq (T₁ := 5) (T₂ := 307)
    (denseOfTailRegCode_exec (by omega) (by decide) hw hN_pos hnU hU hb_pos hy2_wf hy2_er
      (by rw [hy2_sz]; exact hsz_meta)
      hd_last_le_N hc_last_lt hy2_rB hy2_21_eq)
    (fun y3 ⟨hy3_st, hy3_wf, hy3_23, hy3_regs⟩ => ?_) (by omega)
  have hy3_st_x : y3.toBitMemoryState = x.toBitMemoryState := hy3_st.trans hy2_st_x
  have hy3_mem : y3.mem = x.mem := congrArg BitMemory.State.mem hy3_st_x
  have hy3_sz : y3.bitSize = x.bitSize := congrArg BitMemory.State.bitSize hy3_st_x
  have hy3_er : EpochRegs U V w N y3 :=
    hy2_er.congr_regs (fun r hr1 _ =>
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega))
  have hy3_20 : y3.regs 20 = b_win + n_win := by
    rw [hy3_regs 20 (by decide) (by decide), hy2_regs 20 (by decide) (by decide),
      hy1_regs 20 (by decide) (by decide)]
    simp +decide [s1, BitRAM.Data.set]
  have hy3_21 : y3.regs 21 = c_last := by
    rw [hy3_regs 21 (by decide) (by decide), hy2_21_eq]
  have hy3_22 : y3.regs 22 = t_rem := by
    rw [hy3_regs 22 (by decide) (by decide), hy2_regs 22 (by decide) (by decide), hy1_22]
    rfl
  refine .seq (T₁ := 195) (T₂ := 112)
    (copyDenseItemRegCode_exec (by decide) (by decide) hw (le_of_lt hU) hV hy3_wf hy3_er
      (by omega) hd_last_lt hy3_20 hy3_23 (by rw [hy3_sz]; exact hsz)
      (by rw [hy3_mem, hm2]) (by rw [hy3_mem, hm3]))
    (fun y4 ⟨hy4_wf, hy4_er, hy4_sz, hy4_q, hy4_v, hy4_other, hy4_meta, hy4_regs⟩ => ?_)
    (by omega)
  have hy4_sz_x : y4.bitSize = x.bitSize := hy4_sz.trans hy3_sz
  have hy4_td : tdAtBit U w N y4.mem = td := by
    funext i; unfold td tdAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_dt : dtAtBit U w N y4.mem = dt := by
    funext i; unfold dt dtAtBit
    by_cases hi : i < maxTailItems N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by rw [← offDT_add_eq_epochMetaWords hN_pos]; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_gm : gmAtBit U w N y4.mem = gmAtBit U w N x.mem := by
    funext i; unfold gmAtBit
    by_cases hi : i < globalMetaLen N
    · rw [ite_eq_left hi, ite_eq_left hi]
      exact readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr (by
          rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD; omega)).trans
          (congrFun hy3_mem addr)) hi
    · rw [ite_eq_right hi, ite_eq_right hi]
  have hy4_lm : lmAtBit U w N y4.mem = lmAtBit U w N x.mem := by
    funext ⟨c, j⟩; unfold lmAtBit; dsimp only
    by_cases hcj : c < 9 ∧ j < totalMicroBuckets N
    · rw [ite_eq_left hcj, ite_eq_left hcj]
      apply readPacked_congr hw (fun addr haddr =>
        (hy4_meta addr ?_).trans (congrFun hy3_mem addr)) hcj.2
      have hmul : (c + 1) * Succinct.lmSubWords N w ≤ 9 * Succinct.lmSubWords N w :=
        Nat.mul_le_mul_right _ hcj.1
      have haddr_hi := haddr.2
      unfold offLMSub at haddr_hi
      rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT offTD offGM
      rw [lmSubWords_eq] at hmul haddr_hi ⊢
      rw [Nat.add_one_mul] at hmul
      omega
    · rw [ite_eq_right hcj, ite_eq_right hcj]
  refine .seq (T₁ := 56) (T₂ := 56)
    (writeTDRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy4_wf hy4_er
      ht_rem_lt hclast_val (by rw [hy4_regs 22 (by decide), hy3_22])
      (by rw [hy4_regs 21 (by decide), hy3_21]) (by rw [hy4_sz_x]; exact hsz_meta))
    (fun y5 ⟨hy5_sz, hy5_wf, hy5_er, hy5_td, hy5_gm, hy5_lm, hy5_dt, hy5_out, hy5_items,
      hy5_regs⟩ => ?_) (by omega)
  refine (writeDTRegCode_exec (by decide) (by decide) hw hN_pos hnU hU hy5_wf hy5_er
    hc_last_lt htrem_val
    (by rw [hy5_regs 21 (by decide), hy4_regs 21 (by decide), hy3_21])
    (by rw [hy5_regs 22 (by decide), hy4_regs 22 (by decide), hy3_22])
    (by rw [hy5_sz, hy4_sz_x]; exact hsz_meta)).mono
    (fun y ⟨hy_sz, hy_wf, hy_er, hy_dt, hy_gm, hy_lm, hy_td, hy_out, hy_items, hy_regs⟩ => ?_)
    le_rfl
  refine ⟨hy_sz.trans (hy5_sz.trans hy4_sz_x), hy_wf, hy_er,
    hy_td.trans (hy5_td.trans (by rw [hy4_td]; rfl)),
    hy_dt.trans (by rw [hy5_dt, hy4_dt]; rfl),
    hy_gm.trans (hy5_gm.trans hy4_gm),
    hy_lm.trans (hy5_lm.trans hy4_lm),
    fun a ha => (hy_out a (Or.inl (by unfold offDT; omega))).trans
      ((hy5_out a (Or.inl ha)).trans
        ((hy4_meta a (by rw [← offDT_add_eq_epochMetaWords hN_pos]; unfold offDT; omega)).trans
          (congrFun hy3_mem a))),
    fun d hd => ?_,
    fun r hr => ?_⟩
  · rw [(hy_items d).1, (hy_items d).2, (hy5_items d).1, (hy5_items d).2]
    by_cases heq : d = d_last
    · subst heq
      rw [ite_eq_left rfl, hy4_q, hy4_v, hy3_st_x]
      exact ⟨rfl, rfl⟩
    · rw [ite_eq_right heq]
      obtain ⟨hq_o, hv_o⟩ := hy4_other d (by omega) heq
      rw [hy3_st_x] at hq_o hv_o
      exact ⟨hq_o, hv_o⟩
  · rw [hy_regs r (by omega), hy5_regs r (by omega), hy4_regs r (by omega),
      hy3_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy2_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega),
      hy1_regs r (by omega) (by intro h; have := congrArg Fin.val h; omega)]
    dsimp only [s1, BitRAM.Data.set]
    repeat rw [Function.update_of_ne (by intro h; have := congrArg Fin.val h; omega)]


end Cslib.DataStructure.Dictionary.BitResizable
