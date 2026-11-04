/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Transition

/-!
# Client Subroutine Theorems for the Bit-Resizable Succinct Dictionary

This module proves Deliverable (d): client subroutine theorems demonstrating how an external
caller uses the bit-resizable succinct dictionary as a subroutine on the single linear
bit-resizable memory `[0, s.bitSize)` of `BitRAM`, and how bits released when keys are deleted
are immediately reusable by other data structures or client allocations in the same memory.

## Main definitions

* `Cslib.DataStructure.Dictionary.BitResizable.clientAllocBitsCode`: concrete
  `BitRAM.Code .standard 12` client subroutine that grows the bit-resizable memory by `b` bits
  (`b ≤ w`) and writes a `b`-bit client value `v` into the newly allocated bit interval
  `[y.bitSize, y.bitSize + b)` in `46` machine instructions under demonic `.grow`.

## Main results

* `clientAllocBitsCode_exec`: under demonic `.grow`, `clientAllocBitsCode b v` executes in at most
  `46` `BitRAM` instructions, deterministically writes `v` into `[y.bitSize, y.bitSize + b)`, and
  preserves every existing bit in `[0, y.bitSize)`.
* `delete_reuses_released_bits_subroutine`: when a client deletes an active key `u` from the
  dictionary (`(s_abs u).isSome`) within an epoch and then allocates a `b`-bit client field
  (`b ≤ itemBits U V N`, `b ≤ w`), the deletion shrinks `bitSize` by `itemBits U V N` bits and the
  subsequent client allocation reuses the released bit interval
  `[x.bitSize - itemBits U V N, x.bitSize - itemBits U V N + b)` inside
  `[x.bitSize - itemBits U V N, x.bitSize)`
  so that total live bit usage `z.bitSize ≤ x.bitSize` never exceeds the pre-delete bit footprint,
  while preserving the post-delete dictionary representation on `[0, x.bitSize - itemBits U V N)`
  and maintaining `O(1)` expected amortized instruction cost.
* `dict_subroutine_with_delete_reuse_from_empty`: end-to-end client theorem from an empty `BitRAM`
  (`x₀.bitSize = 0`) combining initialization (`initDictCode`), an arbitrary valid dictionary
  history `ops : List (Dynamic.Op U)` with tight pointwise bit-space
  `OPT(U, V, n_t) + O(n_t log₂ log₂(max n_t 4)) + 218 * w` at every step `t`, and bit-level reuse
  of released memory upon deletion.
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

/-! ## Section 1: Client bit-allocation primitive (`clientAllocBitsCode`) -/

/-- Concrete `BitRAM.Code .standard 12` client subroutine that grows the bit-resizable memory by
`b` bits (`b ≤ w`) and writes the `b`-bit value `v` (`Fits b v`) into the newly allocated bit
interval `[y.bitSize, y.bitSize + b)` in at most `46` machine instructions under demonic `.grow`. -/
@[expose]
def clientAllocBitsCode (b v : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 b))
    (.seq (.grow 1 1)
      (.seq (.op (.const 2 b))
        (.seq (.op (.const 3 v))
          BitRAM.writeBitsCode)))

/-- **Demonic execution certificate for `clientAllocBitsCode`:**
from any well-formed state `y : BitRAM.Data 12` with `Fits w (y.bitSize + b)`, `b ≤ w`, and
`Fits b v`, `clientAllocBitsCode b v` executes in at most `46` `BitRAM` instructions under demonic
`.grow`, producing a well-formed state `z` with:
1. `z.bitSize = y.bitSize + b`,
2. `z.toBitMemoryState.getField w y.bitSize b = v`, and
3. `∀ i < y.bitSize, z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i` (all lower bits
   belonging to earlier data structures in `[0, y.bitSize)` are preserved). -/
theorem clientAllocBitsCode_exec {w b v : ℕ} (hw : 0 < w) (hbw : b ≤ w) (hv : Fits b v)
    {y : BitRAM.Data 12} (hy : y.WellFormed w) (hgrow_fits : Fits w (y.bitSize + b)) :
    BitRAM.DemonicExecWithin w (clientAllocBitsCode b v) y
      (fun z =>
        z.WellFormed w ∧
        z.bitSize = y.bitSize + b ∧
        z.toBitMemoryState.getField w y.bitSize b = v ∧
        (∀ i < y.bitSize,
          z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i))
      46 := by
  have hb_fits : Fits w b := Fits.of_le (fits_self w) hbw
  have hv_fits : Fits w v := hv.mono hbw
  refine DemonicExecWithin.step_const (T := 45) hb_fits ?_
  have hcost_grow : max 1 (b ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hbw y.toBitMemoryState).le
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w y.toBitMemoryState (.grow b) s₁ y.bitSize ∧
        y₁ = ⟨Function.update (y.set 1 b).regs 1 y.bitSize, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 44)
    (.grow hgrow_fits hcost_grow fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  refine DemonicExecWithin.step_const (T := 43) hb_fits ?_
  refine DemonicExecWithin.step_const (T := 42) hv_fits ?_
  let y₂ : BitRAM.Data 12 :=
    ((⟨Function.update (y.set 1 b).regs 1 y.bitSize, s₁.mem, s₁.bitSize⟩ :
      BitRAM.Data 12).set 2 b).set 3 v
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep hw hy.mem_wf
      (show BitMemory.valid w y.toBitMemoryState (.grow b) from hgrow_fits) hs₁
  have hy₂_wf : y₂.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi3 : i = 3
    · subst hi3; exact hv_fits
    · by_cases hi2 : i = 2
      · subst hi2
        simp only [y₂, BitRAM.Data.set, Function.update_of_ne hi3, Function.update_self]
        exact hb_fits
      · by_cases hi1 : i = 1
        · subst hi1
          simp only [y₂, BitRAM.Data.set, Function.update_of_ne hi3, Function.update_of_ne hi2,
            Function.update_self]
          exact hy.mem_wf.bitSize_fits
        · simp only [y₂, BitRAM.Data.set, Function.update_of_ne hi3, Function.update_of_ne hi2,
            Function.update_of_ne hi1]
          exact hy.regs_fits i
  have hv_write : BitMemory.valid w y₂.toBitMemoryState
      (.writeBits (y₂.regs 1) (y₂.regs 2) (y₂.regs 3)) := by
    refine ⟨hbw, ?_, hv⟩
    change y.bitSize + b ≤ s₁.bitSize
    rw [hs₁.1]
    exact le_rfl
  refine (writeBitsCode_exec_wf hw hy₂_wf hv_write).mono (fun z ⟨hz_st, hz_wf⟩ => ?_) le_rfl
  change z.toBitMemoryState =
    ⟨writeFieldMem w 0 s₁.mem y.bitSize b v, s₁.bitSize⟩ at hz_st
  have hmem_eq : writeFieldMem w 0 s₁.mem y.bitSize b v =
      writeFieldMem w 0 y.mem y.bitSize b v :=
    writeFieldMem_of_dirtyStep_grow hw hy.mem_wf hbw hs₁
  have hz_mem : z.mem = writeFieldMem w 0 y.mem y.bitSize b v := by
    have h1 : z.mem = writeFieldMem w 0 s₁.mem y.bitSize b v :=
      congrArg BitMemory.State.mem hz_st
    exact h1.trans hmem_eq
  have hz_sz : z.bitSize = y.bitSize + b := by
    have h1 : z.bitSize = s₁.bitSize := congrArg BitMemory.State.bitSize hz_st
    exact h1.trans hs₁.1
  refine ⟨hz_wf, hz_sz, ?_, ?_⟩
  · unfold BitMemory.State.getField
    change readField w 0 z.mem y.bitSize b = v
    rw [hz_mem, readField_writeFieldMem_same hw y.mem hbw hv]
  · intro i hi
    unfold BitMemory.State.getBit
    change readBit w 0 z.mem i = readBit w 0 y.mem i
    rw [hz_mem, readBit_writeFieldMem hw y.mem hbw i, ite_eq_right (by omega)]

/-! ## Section 2: Subroutine composition and reuse of bits released by `delete` -/

/-- **Client subroutine theorem (`delete_reuses_released_bits_subroutine`):**
suppose `DictInv U V w N θ s_abs c x` holds at `x : BitRAM.Data 12`, key `u : Fin U` is active in
`s_abs` (`(s_abs u).isSome`), and the post-delete key count still satisfies `EpochInv U N m'`.
Let `b ≤ itemBits U V N` (`b ≤ w`) and `v_client < 2 ^ b`.
Then there exist a post-delete companion `c'`, a concrete dictionary deletion program
`code_del : BitRAM.Code .standard 12`, and a step bound `T : ℕ` such that:
1. Executing `code_del` from `x` takes at most `T` instructions under demonic `.grow` and produces a
   dictionary state `y` satisfying `DictInv U V w N θ (nextState s_abs (.delete u)) c' y` with
   shrunk bit allocation `y.bitSize = x.bitSize - itemBits U V N` (releasing the trailing
   `itemBits U V N` bits `[y.bitSize, x.bitSize)`).
2. Immediately executing the client subroutine `clientAllocBitsCode b v_client` after `code_del`
   (i.e. `.seq code_del (clientAllocBitsCode b v_client)`) executes in at most `T + 46` machine
   instructions under demonic `.grow` and produces a state `z` that:
   * reuses the released bit interval
     `[x.bitSize - itemBits U V N, x.bitSize - itemBits U V N + b)` inside
     `[x.bitSize - itemBits U V N, x.bitSize)` with total live bit allocation
     `z.bitSize = x.bitSize - itemBits U V N + b ≤ x.bitSize` never exceeding the pre-delete bit
     footprint `x.bitSize`,
   * stores the client's `b`-bit field
     `z.toBitMemoryState.getField w (x.bitSize - itemBits U V N) b = v_client`,
   * preserves every dictionary bit in `[0, x.bitSize - itemBits U V N)`
     (`z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i` for all
     `i < x.bitSize - itemBits U V N`), and
3. `T + totalPotential U V w N (nextState s_abs (.delete u)) c' ≤`
   `totalPotential U V w N s_abs c + stepOverhead U N θ s_abs (.delete u)`, where the expected value
   of `stepOverhead` over `θ ← epochSeedPMF U N` is at most `8034` (`O(1)` expected amortized
   instructions). -/
theorem delete_reuses_released_bits_subroutine {U V w N : ℕ} (hw : 4 ≤ w)
    (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U} {c : Companion}
    {x : BitRAM.Data 12} (hinv : DictInv U V w N θ s_abs c x)
    (u : Fin U) (hsome : (s_abs u).isSome)
    (hepoch' : EpochInv U N (Dynamic.dom (nextState s_abs (.delete u))).card)
    {b v_client : ℕ} (hbw : b ≤ w) (hb_item : b ≤ itemBits U V N) (hv_client : Fits b v_client) :
    let s_abs' := nextState s_abs (.delete u)
    let bit_after_del := x.bitSize - itemBits U V N
    ∃ (c' : Companion) (code_del : BitRAM.Code .standard 12) (T : ℕ),
      T + totalPotential U V w N s_abs' c' ≤
        totalPotential U V w N s_abs c + stepOverhead U N θ s_abs (.delete u) ∧
      (∑' θ₀ : Succinct.QuotHashSeed U N,
        (epochSeedPMF U N θ₀ : ℝ≥0∞) *
          ((stepOverhead U N θ₀ s_abs (.delete u) : ℕ) : ℝ≥0∞)) ≤ 8034 ∧
      BitRAM.DemonicExecWithin w (.seq code_del (clientAllocBitsCode b v_client)) x
        (fun z =>
          ∃ y : BitRAM.Data 12,
            DictInv U V w N θ s_abs' c' y ∧
            y.bitSize = bit_after_del ∧
            z.WellFormed w ∧
            z.bitSize = bit_after_del + b ∧
            z.bitSize ≤ x.bitSize ∧
            z.toBitMemoryState.getField w bit_after_del b = v_client ∧
            (∀ i < bit_after_del,
              z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i))
        (T + 46) := by
  have hw0 : 0 < w := by omega
  let s_abs' := nextState s_abs (.delete u)
  let m := (Dynamic.dom s_abs).card
  let m' := (Dynamic.dom s_abs').card
  have hm_pos : 0 < m := Finset.card_pos.mpr ⟨u, mem_dom_iff_isSome.mpr hsome⟩
  have hcard_del : m' = m - 1 := Dynamic.card_dom_delete_eq_of_isSome hsome
  have hx_sz : x.bitSize = dictBitSize U V w N m := hinv.bitSize_eq
  have hdict_sub : dictBitSize U V w N m' = x.bitSize - itemBits U V N := by
    rw [hx_sz, hcard_del]
    unfold dictBitSize
    have hmul : m * itemBits U V N = (m - 1) * itemBits U V N + itemBits U V N := by
      conv_lhs => rw [← Nat.sub_add_cancel (show 1 ≤ m from hm_pos), Nat.add_one_mul]
    omega
  obtain ⟨c', code_del, T, _, hexec_del, hcost⟩ :=
    step_transition_inEpoch hw hU hV θ hinv (.delete u) trivial hepoch'
  have htsum := tsum_stepOverhead_le hinv.valid.epoch (.delete u)
  refine ⟨c', code_del, T, hcost, htsum, ?_⟩
  refine .seq (T₁ := T) (T₂ := 46) hexec_del (fun y ⟨hinv_y, _⟩ => ?_) (by omega)
  have hy_sz : y.bitSize = x.bitSize - itemBits U V N := by
    rw [hinv_y.bitSize_eq]
    exact hdict_sub
  have hib_le : itemBits U V N ≤ x.bitSize := by
    rw [hx_sz]
    unfold dictBitSize
    have : 1 * itemBits U V N ≤ m * itemBits U V N := Nat.mul_le_mul_right _ hm_pos
    omega
  have hgrow_le : y.bitSize + b ≤ x.bitSize := by
    rw [hy_sz]
    omega
  have hgrow_fits : Fits w (y.bitSize + b) :=
    Fits.of_le hinv.wf.mem_wf.bitSize_fits hgrow_le
  refine (clientAllocBitsCode_exec hw0 hbw hv_client hinv_y.wf hgrow_fits).mono
    (fun z ⟨hz_wf, hz_sz, hz_field, hz_bits⟩ => ?_) le_rfl
  refine ⟨y, hinv_y, hy_sz, hz_wf, ?_, ?_, ?_, ?_⟩
  · rw [← hy_sz]; exact hz_sz
  · rw [hz_sz]; exact hgrow_le
  · rw [← hy_sz]; exact hz_field
  · intro i hi
    exact hz_bits i (by omega)

/-- **End-to-end client theorem from empty (`dict_subroutine_with_delete_reuse_from_empty`):**
starting from an empty `BitRAM` (`x₀.bitSize = 0`, `x₀.WellFormed w`), a client can:
1. initialize the bit-resizable dictionary (`initDictCode`) in `21` instructions (`4 * w` bits) and
   execute any valid operation sequence `ops : List (Dynamic.Op U)` with:
   * pointwise bit-space
     `x_t.bitSize ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`
     at every step `t` in the current active key count `n_t`,
   * exact register answers `decodeQueryRegs y = s_t u` for every `.query u`, and
   * telescoped instruction sum `ts.sum ≤ B_tot` where each step's amortized overhead has
     expectation at most `8034` (`O(1)` expected amortized instructions), and
2. at any intermediate or final dictionary state `x` with an active key `u` (`(s_abs u).isSome`)
   satisfying `EpochInv U N m'`, delete `u` and immediately reuse
   `[x.bitSize - itemBits U V N, x.bitSize - itemBits U V N + b)` for a `b`-bit client field
   (`b ≤ itemBits U V N`, `b ≤ w`) via `delete_reuses_released_bits_subroutine` without increasing
   live bit usage above `x.bitSize`. -/
theorem dict_subroutine_with_delete_reuse_from_empty {U V w : ℕ} (hw : 4 ≤ w)
    (hU : Fits w U) (hV : V ≤ 2 ^ w)
    (hfit_all : ∀ N' ≤ U, Fits w (dictBitSize U V w N' N'))
    (θ₀ : Succinct.QuotHashSeed U 0)
    {x₀ : BitRAM.Data 12} (hx_wf : x₀.WellFormed w) (hx_sz : x₀.bitSize = 0)
    (ops : List (Dynamic.Op U)) (hvh : (spec U V).ValidHistory (Dynamic.empty U) ops) :
    (∃ B_tot : ℕ,
      BitRAM.DemonicExecWithin w (initDictCode U V w θ₀) x₀
        (fun y₀ =>
          DictInv U V w 0 θ₀ (Dynamic.empty U) Companion.empty y₀ ∧
          y₀.bitSize = 4 * w ∧
          ExecTrace U V w ops 0 θ₀ (Dynamic.empty U) Companion.empty y₀ B_tot ∧
          ∃ ts : List ℕ, ts.length = ops.length ∧ ts.sum ≤ B_tot)
        21) ∧
    (∀ {N : ℕ} (θ : Succinct.QuotHashSeed U N) {s_abs : Dynamic.State U}
        {c : Companion} {x : BitRAM.Data 12}
        (_ : DictInv U V w N θ s_abs c x)
        (u : Fin U) (_ : (s_abs u).isSome)
        (_ : EpochInv U N (Dynamic.dom (nextState s_abs (.delete u))).card)
        {b v_client : ℕ} (_ : b ≤ w) (_ : b ≤ itemBits U V N) (_ : Fits b v_client),
      let s_abs' := nextState s_abs (.delete u)
      let bit_after_del := x.bitSize - itemBits U V N
      ∃ (c' : Companion) (code_del : BitRAM.Code .standard 12) (T : ℕ),
        T + totalPotential U V w N s_abs' c' ≤
          totalPotential U V w N s_abs c + stepOverhead U N θ s_abs (.delete u) ∧
        BitRAM.DemonicExecWithin w (.seq code_del (clientAllocBitsCode b v_client)) x
          (fun z =>
            ∃ y : BitRAM.Data 12,
              DictInv U V w N θ s_abs' c' y ∧
              y.bitSize = bit_after_del ∧
              z.WellFormed w ∧
              z.bitSize = bit_after_del + b ∧
              z.bitSize ≤ x.bitSize ∧
              z.toBitMemoryState.getField w bit_after_del b = v_client ∧
              (∀ i < bit_after_del,
                z.toBitMemoryState.getBit w i = y.toBitMemoryState.getBit w i))
          (T + 46)) := by
  refine ⟨seq_transition_from_empty hw hU hV hfit_all θ₀ hx_wf hx_sz ops hvh, ?_⟩
  intro N θ s_abs c x hinv u hsome hepoch' b v_client hbw hb_item hv_client
  obtain ⟨c', code_del, T, hcost, _, hexec⟩ :=
    delete_reuses_released_bits_subroutine hw hU hV θ hinv u hsome hepoch' hbw hb_item hv_client
  exact ⟨c', code_del, T, hcost, hexec⟩

end Cslib.DataStructure.Dictionary.BitResizable
