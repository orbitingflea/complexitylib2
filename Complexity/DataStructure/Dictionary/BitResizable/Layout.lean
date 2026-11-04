/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.DataStructure.Dictionary.BitResizable.Spec
public import Complexity.DataStructure.Memory.BitResizable
public import Complexity.Computability.WordRAM.BitResizable

/-!
# Bit-Resizable Succinct Dictionary Layout, Compaction Bijection, and Demonic Item Primitives

This module defines the single-tape bit-resizable memory layout (`[0, s_bit.bitSize)`) for the
bit-resizable succinct dictionary, the circular tail-to-dense slot bijection (`TailDenseInv` and
`denseOfPhys`) that packs all `n_t` active `(quotient, value)` items into a zero-gap suffix of
`n_t * itemBits U V N` bits, the full representation invariant (`Rep`), and the demonic
bit-resizable item primitives (`appendDenseItemProg`, `popDenseItemProg`, `readDenseItemProg`,
`writeDenseItemProg`) together with their concrete `BitRAM.Code` realizations and
`BitRAM.DemonicExecWithin` machine-instruction bounds.

## Single-tape layout (`[0, dictBitSize U V w N n_t)`)

1. **Header (`[0, 4 * w)` bits = words `0 .. 3`):**
   * word `0`: `n_t = (Dynamic.dom s_abs).card` (current active key count),
   * word `1`: `N` (current epoch capacity parameter: `0` when `n_t = 0`, else `n_t ≤ N ≤ 4 * n_t`),
   * word `2`: `itemBits U V N = quotientBits U N + valBits V`,
   * word `3`: `epochMetaBits U w N = epochMetaWords U w N * w`.
2. **Epoch metadata prefix (`[4 * w, epochMetaBits U w N)` bits, present when `N > 0`):**
   * `[offHash, offLM)`: `Succinct.hashSpace U w N` words for the two-stage 3-wise independent
     quotient hash family (`ReducedKWise`),
   * `[offLM, offGM)`: `9 * Succinct.lmSubWords N w` words for the 9 `LocalMeta` sub-arrays,
   * `[offGM, offTD)`: `packedWords (globalMetaLen N) (globalPtrBits N) w` words for `GlobalMeta`,
   * `[offTD, offDT)`: `packedWords (maxTailItems N) (globalPtrBits N) w` words for `TailDense`,
   * `[offDT, epochMetaWords U w N)`: `packedWords (maxTailItems N) (globalPtrBits N) w` words for
     `DenseTail`.
3. **Dense bit-resizable item suffix (`[epochMetaBits U w N, dictBitSize U V w N n_t)` bits):**
   * item `d < n_t` occupies `[itemBitOff U V w N d, itemBitOff U V w N (d + 1))`, split into
     its `(quotientBits U N)`-bit quotient at `itemQuotBitOff U V w N d` and its `(valBits V)`-bit
     value at `itemValBitOff U V w N d`.

## Main definitions

* `offHash`, `offLM`, `offLMSub`, `offGM`, `offTD`, `offDT`: word offsets in the metadata prefix.
* `itemBitOff`, `itemQuotBitOff`, `itemValBitOff`, `denseQuotAt`, `denseValAt`: bit offsets and
  field extractors for dense items `d < n_t`.
* `denseOfCirc`, `TailDenseInv`, `denseOfPhys`: circular tail-to-dense bijection mapping active
  physical slots in `[0, N)` bijectively onto dense item indices `[0, n_t)`.
* `virtualQuotAt`, `virtualValAt`, `Rep`: virtual fixed-capacity projections and full
  representation invariant on `BitMemory.State`.
* `appendDenseItemProg`, `popDenseItemProg`, `readDenseItemProg`, `writeDenseItemProg`:
  demonic `BitMemory.Prog` operations for growing, shrinking, reading, and writing dense items.
* `appendDenseItemCode`, `popDenseItemCode`:
  concrete `BitRAM.Code .standard 12` programs with `DemonicExecWithin` instruction bounds.
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

/-! ## Section 1: Single-tape bit-resizable memory offsets and field accessors -/

/-- Word offset `4` of the quotient hash family inside the epoch metadata prefix. -/
@[expose] def offHash : ℕ := 4

/-- Word offset of `LocalMeta` inside the epoch metadata prefix. -/
@[expose] def offLM (U w N : ℕ) : ℕ :=
  offHash + Succinct.hashSpace U w N

/-- Word offset of the `c`-th `LocalMeta` sub-array (`c < 9`). -/
@[expose] def offLMSub (U w N c : ℕ) : ℕ :=
  offLM U w N + c * Succinct.lmSubWords N w

/-- Word offset of `GlobalMeta` inside the epoch metadata prefix. -/
@[expose] def offGM (U w N : ℕ) : ℕ :=
  offLM U w N + 9 * Succinct.lmSubWords N w

/-- Word offset of `TailDense` inside the epoch metadata prefix. -/
@[expose] def offTD (U w N : ℕ) : ℕ :=
  offGM U w N + packedWords (globalMetaLen N) (globalPtrBits N) w

/-- Word offset of `DenseTail` inside the epoch metadata prefix. -/
@[expose] def offDT (U w N : ℕ) : ℕ :=
  offTD U w N + packedWords (maxTailItems N) (globalPtrBits N) w

/-- When `N > 0`, `offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w` equals
`epochMetaWords U w N`. -/
theorem offDT_add_eq_epochMetaWords {U w N : ℕ} (hN : 0 < N) :
    offDT U w N + packedWords (maxTailItems N) (globalPtrBits N) w =
      epochMetaWords U w N := by
  have hne : N ≠ 0 := Nat.ne_of_gt hN
  unfold epochMetaWords offDT offTD offGM offLM offHash
  rw [ite_eq_right hne]
  ring

/-- Bit offset of dense item `d` inside the bit-resizable memory `s_bit`. -/
@[expose] def itemBitOff (U V w N d : ℕ) : ℕ :=
  epochMetaBits U w N + d * itemBits U V N

/-- Bit offset of the `(quotientBits U N)`-bit quotient field of dense item `d`. -/
@[expose] def itemQuotBitOff (U V w N d : ℕ) : ℕ :=
  itemBitOff U V w N d

/-- Bit offset of the `(valBits V)`-bit value field of dense item `d`. -/
@[expose] def itemValBitOff (U V w N d : ℕ) : ℕ :=
  itemBitOff U V w N d + quotientBits U N

@[simp]
theorem itemBitOff_zero (U V w N : ℕ) :
    itemBitOff U V w N 0 = epochMetaBits U w N := by
  simp [itemBitOff]

theorem itemBitOff_succ (U V w N d : ℕ) :
    itemBitOff U V w N (d + 1) = itemBitOff U V w N d + itemBits U V N := by
  unfold itemBitOff
  ring

theorem itemValBitOff_add_valBits (U V w N d : ℕ) :
    itemValBitOff U V w N d + valBits V = itemBitOff U V w N (d + 1) := by
  unfold itemValBitOff itemBitOff itemBits
  ring

theorem itemBitOff_eq_dictBitSize (U V w N n_t : ℕ) :
    itemBitOff U V w N n_t = dictBitSize U V w N n_t :=
  rfl

/-- Extract the quotient of dense item `d` from `s_bit : BitMemory.State`. -/
@[expose] def denseQuotAt (U V w N : ℕ) (s_bit : BitMemory.State) (d : ℕ) : ℕ :=
  s_bit.getField w (itemQuotBitOff U V w N d) (quotientBits U N)

/-- Extract the value of dense item `d` from `s_bit : BitMemory.State`. -/
@[expose] def denseValAt (U V w N : ℕ) (s_bit : BitMemory.State) (d : ℕ) : ℕ :=
  s_bit.getField w (itemValBitOff U V w N d) (valBits V)

/-- Extract `LocalMeta` entry `(c, idx)` from `mem : ℕ → ℕ`. -/
@[expose] def lmAtBit (U w N : ℕ) (mem : ℕ → ℕ) (p : ℕ × ℕ) : ℕ :=
  if p.1 < 9 ∧ p.2 < totalMicroBuckets N then
    readPacked (offLMSub U w N p.1) (effBucketPosBits N) w mem p.2
  else 0

/-- Extract `GlobalMeta` entry `idx` from `mem : ℕ → ℕ`. -/
@[expose] def gmAtBit (U w N : ℕ) (mem : ℕ → ℕ) (idx : ℕ) : ℕ :=
  if idx < globalMetaLen N then
    readPacked (offGM U w N) (globalPtrBits N) w mem idx
  else 0

/-- Extract `TailDense` entry `t < maxTailItems N` from `mem : ℕ → ℕ`. -/
@[expose] def tdAtBit (U w N : ℕ) (mem : ℕ → ℕ) (t : ℕ) : ℕ :=
  if t < maxTailItems N then
    readPacked (offTD U w N) (globalPtrBits N) w mem t
  else 0

/-- Extract `DenseTail` entry `c < maxTailItems N` from `mem : ℕ → ℕ`. -/
@[expose] def dtAtBit (U w N : ℕ) (mem : ℕ → ℕ) (c : ℕ) : ℕ :=
  if c < maxTailItems N then
    readPacked (offDT U w N) (globalPtrBits N) w mem c
  else 0

theorem denseQuotAt_lt (U V w N : ℕ) (s_bit : BitMemory.State) (d : ℕ) :
    denseQuotAt U V w N s_bit d < 2 ^ quotientBits U N :=
  readField_lt w 0 s_bit.mem _ _

theorem denseValAt_lt (U V w N : ℕ) (s_bit : BitMemory.State) (d : ℕ) :
    denseValAt U V w N s_bit d < 2 ^ valBits V :=
  readField_lt w 0 s_bit.mem _ _

/-! ## Section 2: Circular tail-to-dense compaction bijection (`TailDenseInv`, `denseOfPhys`) -/

/-- Recover the unique integer `d ∈ [base_tail, base_tail + M)` satisfying `d % M = c` (for
`0 < M` and `c < M`). Because `d` depends only on `c = d % M` and `base_tail`, advancing
`base_tail` by `+K` on slab promotion or `-K` on slab demotion leaves `d % M` invariant for all
unmoved tail items. -/
@[expose] def denseOfCirc (M base_tail c : ℕ) : ℕ :=
  if M = 0 then base_tail
  else base_tail + (c + M - base_tail % M) % M

/-- For any `M > 0` and `d ∈ [base_tail, base_tail + M)`, `denseOfCirc M base_tail (d % M) = d`. -/
theorem denseOfCirc_mod_self {M base_tail d : ℕ} (hM : 0 < M)
    (hlo : base_tail ≤ d) (hhi : d < base_tail + M) :
    denseOfCirc M base_tail (d % M) = d := by
  have hM0 : M ≠ 0 := Nat.ne_of_gt hM
  unfold denseOfCirc
  rw [ite_eq_right hM0]
  set δ := d - base_tail
  have hδ_lt : δ < M := by omega
  have hd_eq : d = base_tail + δ := (Nat.add_sub_of_le hlo).symm
  set r := base_tail % M
  have hr_lt : r < M := Nat.mod_lt base_tail hM
  have hd_mod : d % M = (r + δ) % M := by
    conv_lhs => rw [hd_eq, ← Nat.div_add_mod base_tail M, Nat.add_assoc, Nat.mul_add_mod]
  have hmod : (d % M + M - r) % M = δ := by
    by_cases hlt : r + δ < M
    · have hrm : (r + δ) % M = r + δ := Nat.mod_eq_of_lt hlt
      have h1 : (r + δ) + M - r = δ + 1 * M := by omega
      rw [hd_mod, hrm, h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hδ_lt]
    · have hrm : (r + δ) % M = r + δ - M := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      have h1 : (r + δ - M) + M - r = δ := by omega
      rw [hd_mod, hrm, h1, Nat.mod_eq_of_lt hδ_lt]
  omega

/-- For any `M > 0` and `c < M`, `denseOfCirc M base_tail c % M = c`. -/
theorem denseOfCirc_mod {M base_tail c : ℕ} (hM : 0 < M) (hc : c < M) :
    denseOfCirc M base_tail c % M = c := by
  have hM0 : M ≠ 0 := Nat.ne_of_gt hM
  unfold denseOfCirc
  rw [ite_eq_right hM0]
  have hbm : base_tail % M < M := Nat.mod_lt base_tail hM
  have hdiv_b := Nat.div_add_mod base_tail M
  by_cases hle : base_tail % M ≤ c
  · have h1 : (c + M - base_tail % M) % M = c - base_tail % M := by
      have heq : c + M - base_tail % M = (c - base_tail % M) + 1 * M := by omega
      rw [heq, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
    rw [h1]
    have hsum : base_tail + (c - base_tail % M) = c + M * (base_tail / M) := by omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]
  · have h1 : (c + M - base_tail % M) % M = c + M - base_tail % M :=
      Nat.mod_eq_of_lt (by omega)
    rw [h1]
    have hsum : base_tail + (c + M - base_tail % M) = c + M * (base_tail / M + 1) := by
      calc base_tail + (c + M - base_tail % M)
          = (M * (base_tail / M) + base_tail % M) + (c + M - base_tail % M) := by
            rw [hdiv_b]
        _ = c + M * (base_tail / M + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
            omega
    rw [hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hc]

/-- Circular bijection invariant between active tail indices `t ∈ [0, n_tails)` and dense tail
slots `d ∈ [base_tail, base_tail + n_tails)` (where `base_tail = n_slabs * slabSize N` and
`M = maxTailItems N`). -/
structure TailDenseInv (N n_slabs n_tails : ℕ) (td dt : ℕ → ℕ) : Prop where
  /-- Every active tail index `t < n_tails` maps to a circular residue `< maxTailItems N`. -/
  td_lt : ∀ t < n_tails, td t < maxTailItems N
  /-- Every active tail index `t < n_tails` resolves via `denseOfCirc` into the dense tail range
  `[n_slabs * slabSize N, n_slabs * slabSize N + n_tails)`. -/
  dense_lt : ∀ t < n_tails,
    denseOfCirc (maxTailItems N) (n_slabs * slabSize N) (td t) <
      n_slabs * slabSize N + n_tails
  /-- `dt` is a left inverse of `td` on `[0, n_tails)`. -/
  dt_td : ∀ t < n_tails, dt (td t) = t
  /-- Every dense slot `d ∈ [n_slabs * slabSize N, n_slabs * slabSize N + n_tails)` has a valid
  owner `dt (d % maxTailItems N) < n_tails` with
  `td (dt (d % maxTailItems N)) = d % maxTailItems N`. -/
  owner_valid : ∀ d, n_slabs * slabSize N ≤ d → d < n_slabs * slabSize N + n_tails →
    dt (d % maxTailItems N) < n_tails ∧
    td (dt (d % maxTailItems N)) = d % maxTailItems N

/-- When `n_tails = 0`, `TailDenseInv N n_slabs 0 td dt` holds for any `td` and `dt`. -/
theorem tailDenseInv_zero (N n_slabs : ℕ) (td dt : ℕ → ℕ) :
    TailDenseInv N n_slabs 0 td dt where
  td_lt t ht := by omega
  dense_lt t ht := by omega
  dt_td t ht := by omega
  owner_valid d hlo hhi := by omega

/-- Map a physical slot `phys < N` of the fixed-capacity slot store to its dense item index
`d < n_t`:
* When `bucketBits N = 0`: `phys` (`0 ≤ phys < gm 0 = n_t`).
* When `0 < bucketBits N`:
  * if `phys < gm 0 * slabSize N` (an active full-slab slot), `phys`;
  * otherwise (an active tail slot `t = N - 1 - phys < gm 1`),
    `denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))`. -/
@[expose] def denseOfPhys (N : ℕ) (gm td : ℕ → ℕ) (phys : ℕ) : ℕ :=
  if bucketBits N = 0 then phys
  else if phys < gm 0 * slabSize N then phys
  else denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))

/-- Under `SlotStoreInv N gm` and `TailDenseInv N (gm 0) (gm 1) td dt`, every active logical slot
`(b, j)` (`b < numBuckets N`, `j < bCount N gm b`) maps via `denseOfPhys N gm td (slotOf N gm b j)`
into `[0, Succinct.totalSlots N gm)`, and `denseOfPhys N gm td` is injective across all active
logical slots `(b, j)`. -/
theorem denseOfPhys_slotOf_lt_and_injective {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : Succinct.SlotStoreInv N gm)
    (htd : TailDenseInv N (gm 0) (gm 1) td dt) :
    (∀ b < numBuckets N, ∀ j < Succinct.bCount N gm b,
      denseOfPhys N gm td (Succinct.slotOf N gm b j) < Succinct.totalSlots N gm) ∧
    (∀ b₁ < numBuckets N, ∀ j₁ < Succinct.bCount N gm b₁,
      ∀ b₂ < numBuckets N, ∀ j₂ < Succinct.bCount N gm b₂,
      denseOfPhys N gm td (Succinct.slotOf N gm b₁ j₁) =
        denseOfPhys N gm td (Succinct.slotOf N gm b₂ j₂) →
      b₁ = b₂ ∧ j₁ = j₂) := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · have hB1 : numBuckets N = 1 := by simp [numBuckets, hb0]
    refine ⟨?_, ?_⟩
    · intro b hb j hj
      have hb_eq : b = 0 := by omega
      subst hb_eq
      unfold Succinct.bCount at hj
      simp only [hb0, ↓reduceIte] at hj
      unfold denseOfPhys Succinct.slotOf Succinct.totalSlots
      simp only [hb0, ↓reduceIte]
      exact hj
    · intro b₁ hb₁ j₁ hj₁ b₂ hb₂ j₂ hj₂ heq
      have h1 := (Succinct.slotOf_lt_and_injective hslot).2 b₁ hb₁ j₁ hj₁ b₂ hb₂ j₂ hj₂
      unfold denseOfPhys at heq
      simp only [hb0, ↓reduceIte] at heq
      exact h1 heq
  · have hb_ne : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
    have htail := hslot.multi_tail hb_pos
    have hslab := hslot.multi_slab hb_pos
    have htot_le := hslot.multi_total_le hb_pos
    have hK : 0 < slabSize N := slabSize_pos N
    have htot_eq : Succinct.totalSlots N gm = gm 0 * slabSize N + gm 1 := by
      unfold Succinct.totalSlots
      rw [ite_eq_right hb_ne]
    have hcase : ∀ b < numBuckets N, ∀ j < Succinct.bCount N gm b,
        (j < gm (Succinct.gmQIdx b) * slabSize N ∧
          Succinct.slotOf N gm b j < gm 0 * slabSize N ∧
          denseOfPhys N gm td (Succinct.slotOf N gm b j) = Succinct.slotOf N gm b j) ∨
        (gm (Succinct.gmQIdx b) * slabSize N ≤ j ∧
          gm 0 * slabSize N ≤ denseOfPhys N gm td (Succinct.slotOf N gm b j) ∧
          denseOfPhys N gm td (Succinct.slotOf N gm b j) < gm 0 * slabSize N + gm 1 ∧
          Succinct.slotOf N gm b j =
            N - 1 - gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) ∧
          N - 1 - Succinct.slotOf N gm b j =
            gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) ∧
          gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) < gm 1) := by
      intro b hb j hj
      unfold Succinct.bCount at hj
      simp only [hb_ne, ↓reduceIte, hb] at hj
      by_cases hj_slab : j < gm (Succinct.gmQIdx b) * slabSize N
      · left
        have hs_lt : j / slabSize N < gm (Succinct.gmQIdx b) :=
          Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm])
        have hp_lt : Succinct.slabPtrOf N gm b (j / slabSize N) < gm 0 := by
          rw [hslab.nslabs_eq]
          exact hslab.ptr_lt b hb _ hs_lt
        have hmod_lt : j % slabSize N < slabSize N := Nat.mod_lt j hK
        have hphys_lt : Succinct.slotOf N gm b j < gm 0 * slabSize N := by
          unfold Succinct.slotOf
          simp only [hb_ne, ↓reduceIte, hj_slab]
          have h1 : (Succinct.slabPtrOf N gm b (j / slabSize N) + 1) * slabSize N ≤
              gm 0 * slabSize N := Nat.mul_le_mul_right _ hp_lt
          rw [Nat.add_one_mul] at h1
          omega
        refine ⟨hj_slab, hphys_lt, ?_⟩
        unfold denseOfPhys
        simp only [hb_ne, ↓reduceIte, hphys_lt]
      · right
        have hr_lt : j - gm (Succinct.gmQIdx b) * slabSize N < gm (Succinct.gmRIdx b) := by omega
        have ht_lt :
            gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N)) < gm 1 := by
          rw [htail.ntails_eq]
          exact htail.ptr_lt b hb _ hr_lt
        set t := gm (Succinct.gmTailPtrIdx N b (j - gm (Succinct.gmQIdx b) * slabSize N))
        have hphys_eq : Succinct.slotOf N gm b j = N - 1 - t := by
          unfold Succinct.slotOf
          simp only [hb_ne, ↓reduceIte, hj_slab]
          rfl
        have hphys_ge : gm 0 * slabSize N ≤ Succinct.slotOf N gm b j := by
          rw [hphys_eq]
          omega
        have hphys_not_lt : ¬Succinct.slotOf N gm b j < gm 0 * slabSize N := by omega
        have hsub_t : N - 1 - Succinct.slotOf N gm b j = t := by
          rw [hphys_eq]
          omega
        have hd_eq : denseOfPhys N gm td (Succinct.slotOf N gm b j) =
            denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t) := by
          unfold denseOfPhys
          simp only [hb_ne, ↓reduceIte, hphys_not_lt, hsub_t]
        have hd_ge : gm 0 * slabSize N ≤ denseOfPhys N gm td (Succinct.slotOf N gm b j) := by
          rw [hd_eq]
          unfold denseOfCirc
          split_ifs <;> omega
        have hd_lt : denseOfPhys N gm td (Succinct.slotOf N gm b j) <
            gm 0 * slabSize N + gm 1 := by
          rw [hd_eq]
          exact htd.dense_lt t ht_lt
        exact ⟨by omega, hd_ge, hd_lt, hphys_eq, hsub_t, ht_lt⟩
    refine ⟨?_, ?_⟩
    · intro b hb j hj
      rw [htot_eq]
      rcases hcase b hb j hj with ⟨_, hlt, heq⟩ | ⟨_, _, hlt, _, _, _⟩
      · omega
      · exact hlt
    · intro b₁ hb₁ j₁ hj₁ b₂ hb₂ j₂ hj₂ heq
      have hinj_slot := (Succinct.slotOf_lt_and_injective hslot).2 b₁ hb₁ j₁ hj₁ b₂ hb₂ j₂ hj₂
      rcases hcase b₁ hb₁ j₁ hj₁ with ⟨_, hlt₁, heq₁⟩ | ⟨_, hge₁, hlt₁, hphys₁, hsub₁, ht₁⟩ <;>
        rcases hcase b₂ hb₂ j₂ hj₂ with ⟨_, hlt₂, heq₂⟩ | ⟨_, hge₂, hlt₂, hphys₂, hsub₂, ht₂⟩
      · rw [heq₁, heq₂] at heq
        exact hinj_slot heq
      · omega
      · omega
      · have hM_pos : 0 < maxTailItems N := by
          have := htail.ntails_le
          omega
        set t₁ := gm (Succinct.gmTailPtrIdx N b₁ (j₁ - gm (Succinct.gmQIdx b₁) * slabSize N))
        set t₂ := gm (Succinct.gmTailPtrIdx N b₂ (j₂ - gm (Succinct.gmQIdx b₂) * slabSize N))
        have hnot₁ : ¬Succinct.slotOf N gm b₁ j₁ < gm 0 * slabSize N := by omega
        have hnot₂ : ¬Succinct.slotOf N gm b₂ j₂ < gm 0 * slabSize N := by omega
        have hd₁ : denseOfPhys N gm td (Succinct.slotOf N gm b₁ j₁) =
            denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t₁) := by
          unfold denseOfPhys
          simp only [hb_ne, ↓reduceIte, hnot₁, hsub₁]
        have hd₂ : denseOfPhys N gm td (Succinct.slotOf N gm b₂ j₂) =
            denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t₂) := by
          unfold denseOfPhys
          simp only [hb_ne, ↓reduceIte, hnot₂, hsub₂]
        rw [hd₁, hd₂] at heq
        have hmod_eq :
            denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t₁) % maxTailItems N =
              denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t₂) % maxTailItems N :=
          congrArg (· % maxTailItems N) heq
        rw [denseOfCirc_mod hM_pos (htd.td_lt t₁ ht₁),
          denseOfCirc_mod hM_pos (htd.td_lt t₂ ht₂)] at hmod_eq
        have ht_eq : t₁ = t₂ := by
          rw [← htd.dt_td t₁ ht₁, ← htd.dt_td t₂ ht₂, hmod_eq]
        have hslot_eq : Succinct.slotOf N gm b₁ j₁ = Succinct.slotOf N gm b₂ j₂ := by
          rw [hphys₁, hphys₂, ht_eq]
        exact hinj_slot hslot_eq

/-! ## Section 3: Virtual fixed-capacity projection and representation invariant `Rep` -/

/-- Virtual quotient array `ℕ → ℕ` induced on physical slots `phys < N` by composing
`denseQuotAt U V w N s_bit` with
`denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)`. -/
@[expose] def virtualQuotAt (U V w N : ℕ) (s_bit : BitMemory.State) (phys : ℕ) : ℕ :=
  if phys < N then
    denseQuotAt U V w N s_bit
      (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem) phys)
  else 0

/-- Virtual value array `ℕ → ℕ` induced on physical slots `phys < N` by composing
`denseValAt U V w N s_bit` with
`denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem)`. -/
@[expose] def virtualValAt (U V w N : ℕ) (s_bit : BitMemory.State) (phys : ℕ) : ℕ :=
  if phys < N then
    denseValAt U V w N s_bit
      (denseOfPhys N (gmAtBit U w N s_bit.mem) (tdAtBit U w N s_bit.mem) phys)
  else 0

/-- Bucket-level representation invariant on `s_bit : BitMemory.State` for epoch capacity parameter
`N > 0`: couples `SlotStoreInv`, `TailDenseInv`, `AllChainsValid`, per-bucket micro-chain
membership, quotient uniqueness, and the Feistel bucket map `B = Succinct.bucketMapOfState U N h1
s_abs` via `virtualQuotAt` and `virtualValAt`. -/
structure BucketRepInv (U V w N : ℕ) (mOf : ℕ → ℕ) (L : ℕ → ℕ → List ℕ)
    (B : ℕ → ℕ → Option ℕ) (s_bit : BitMemory.State) : Prop where
  /-- `GlobalMeta` satisfies `SlotStoreInv`. -/
  hslot : Succinct.SlotStoreInv N (gmAtBit U w N s_bit.mem)
  /-- `TailDense` and `DenseTail` form a valid circular bijection on `[0, gm 1)`. -/
  htd : TailDenseInv N (gmAtBit U w N s_bit.mem 0) (gmAtBit U w N s_bit.mem 1)
    (tdAtBit U w N s_bit.mem) (dtAtBit U w N s_bit.mem)
  /-- `LocalMeta` encodes valid doubly-linked chains `L b m`. -/
  hchains : Succinct.AllChainsValid N (lmAtBit U w N s_bit.mem) L
  /-- Indexed micro-chain membership for local slots `< effBucketCap N`. -/
  hchain_mem : ∀ b < numBuckets N, ∀ m < numMicroPerBucket N, ∀ j,
    j ∈ L b m ↔
      j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b ∧
      j < effBucketCap N ∧
      mOf (virtualQuotAt U V w N s_bit
        (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j)) = m
  /-- Per-bucket quotient uniqueness across all active slots in bucket `b`. -/
  hnodup_q : ∀ b < numBuckets N,
    ∀ j₁ < Succinct.bCount N (gmAtBit U w N s_bit.mem) b,
    ∀ j₂ < Succinct.bCount N (gmAtBit U w N s_bit.mem) b,
    virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j₁) =
    virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j₂) →
    j₁ = j₂
  /-- Every active slot `(b, j)` stores `(q, v)` with `B b q = some v`. -/
  hmap_some : ∀ b < numBuckets N,
    ∀ j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b,
    B b (virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j)) =
    some (virtualValAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j))
  /-- Every present quotient `q` in bucket `b` appears at some active slot `j < bCount N gm b`. -/
  hmap_dom : ∀ b < numBuckets N, ∀ q,
    (B b q).isSome ↔
      ∃ j < Succinct.bCount N (gmAtBit U w N s_bit.mem) b,
        virtualQuotAt U V w N s_bit (Succinct.slotOf N (gmAtBit U w N s_bit.mem) b j) = q

/-- Full representation invariant coupling an abstract dictionary state `s_abs : Dynamic.State U`
with a single-tape bit-resizable memory state `s_bit : BitMemory.State` under epoch capacity
parameter `N` and hash seed `θ : Succinct.QuotHashSeed U N`. -/
structure Rep (U V w N : ℕ) (θ : Succinct.QuotHashSeed U N)
    (s_abs : Dynamic.State U) (s_bit : BitMemory.State) : Prop where
  /-- The underlying bit-resizable memory is well-formed at word width `w`. -/
  wellFormed : s_bit.WellFormed w
  /-- The allocated bit size equals `dictBitSize U V w N (Dynamic.dom s_abs).card`. -/
  bitSize_eq : s_bit.bitSize = dictBitSize U V w N (Dynamic.dom s_abs).card
  /-- The epoch capacity parameter `N` satisfies `EpochInv U N (Dynamic.dom s_abs).card`. -/
  epoch_inv : EpochInv U N (Dynamic.dom s_abs).card
  /-- Every value in `s_abs` is strictly less than `V`. -/
  values_bounded : Dynamic.ValuesBounded V s_abs
  /-- Header word `0` stores the current key count `n_t = (Dynamic.dom s_abs).card`. -/
  hdr_count : s_bit.mem 0 = (Dynamic.dom s_abs).card
  /-- Header word `1` stores the current epoch capacity parameter `N`. -/
  hdr_cap : s_bit.mem 1 = N
  /-- Header word `2` stores `itemBits U V N`. -/
  hdr_itemBits : s_bit.mem 2 = itemBits U V N
  /-- Header word `3` stores `epochMetaBits U w N`. -/
  hdr_metaBits : s_bit.mem 3 = epochMetaBits U w N
  /-- When `0 < N`, the quotient hash table and seed `θ` are represented at word offset `offHash`,
  `totalSlots N gm = (Dynamic.dom s_abs).card`, and `BucketRepInv` holds. -/
  active_inv : 0 < N →
    ReducedKWise.Rep offHash w (Succinct.qBits U N) (Succinct.hashB N)
      (totalMicroBits N) 3 θ s_bit.mem ∧
    Succinct.totalSlots N (gmAtBit U w N s_bit.mem) = (Dynamic.dom s_abs).card ∧
    ∃ L, BucketRepInv U V w N (Succinct.mOfSeed U N θ) L
      (Succinct.bucketMapOfState U N (Succinct.hValOfSeed U N θ) s_abs) s_bit

/-- **Pointwise succinct bit-space bound for any represented state (`rep_bitSize_le_optBits`):**
in every state `s_bit` satisfying `Rep U V w N θ s_abs s_bit` (`0 < w`, `U ≤ 2 ^ w`), the
allocated bit size `s_bit.bitSize` at current key count `n_t = (Dynamic.dom s_abs).card` satisfies
`s_bit.bitSize ≤ Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w`. -/
theorem rep_bitSize_le_optBits {U V w N : ℕ} {θ : Succinct.QuotHashSeed U N}
    {s_abs : Dynamic.State U} {s_bit : BitMemory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hrep : Rep U V w N θ s_abs s_bit) :
    let n_t := (Dynamic.dom s_abs).card
    s_bit.bitSize ≤
      Dynamic.optBits U V n_t + 680 * n_t * Dynamic.logLogFactor n_t + 218 * w := by
  intro n_t
  rw [hrep.bitSize_eq]
  exact dictBitSize_le_optBits hw hU hrep.epoch_inv

/-! ## Section 4: Demonic bit-resizable item primitives and `BitRAM.Code` realizations -/

theorem word_eq_of_readBit_eq {w : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ} {a : ℕ}
    (h₁ : Fits w (mem₁ a)) (h₂ : Fits w (mem₂ a))
    (h : ∀ j < w, readBit w 0 mem₁ (a * w + j) = readBit w 0 mem₂ (a * w + j)) :
    mem₁ a = mem₂ a := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · have hbit := h j hj
    have hdiv : (a * w + j) / w = a := by
      rw [Nat.mul_comm a w, Nat.mul_add_div hw, Nat.div_eq_of_lt hj, Nat.add_zero]
    have hmod : (a * w + j) % w = j := by
      rw [Nat.mul_comm a w, Nat.mul_add_mod, Nat.mod_eq_of_lt hj]
    simpa [readBit, hdiv, hmod] using hbit
  · have hle : w ≤ j := Nat.le_of_not_lt hj
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h₁ (Nat.pow_le_pow_right Nat.two_pos hle)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h₂ (Nat.pow_le_pow_right Nat.two_pos hle))]

/-- Append a dense `(quotient, value)` item `(q, v)` at the end of `s_bit` by growing first by
`quotientBits U N` bits and writing `q`, then growing by `valBits V` bits and writing `v`.
Because both `quotientBits U N ≤ w` and `valBits V ≤ w`, each resize is a single-step admissible
operation under `BitMemory.dirtySpec w`. -/
@[expose] def appendDenseItemProg (U V N q v : ℕ) : BitMemory.Prog Unit := do
  let off_q ← BitMemory.grow (quotientBits U N)
  BitMemory.writeBits off_q (quotientBits U N) q
  let off_v ← BitMemory.grow (valBits V)
  BitMemory.writeBits off_v (valBits V) v

/-- Pop the last dense `(quotient, value)` item from the end of `s_bit`, shrinking `s_bit.bitSize`
first by `valBits V` bits and then by `quotientBits U N` bits, releasing `itemBits U V N` bits back
to the unallocated suffix `[s_bit.bitSize, ∞)`. -/
@[expose] def popDenseItemProg (U V N : ℕ) : BitMemory.Prog (ℕ × ℕ) := do
  let sz₁ ← BitMemory.getSize
  let v ← BitMemory.readBits (sz₁ - valBits V) (valBits V)
  BitMemory.shrink (valBits V)
  let sz₂ ← BitMemory.getSize
  let q ← BitMemory.readBits (sz₂ - quotientBits U N) (quotientBits U N)
  BitMemory.shrink (quotientBits U N)
  pure (q, v)

/-- Read dense item `d` (`(quotient, value)`) in `BitMemory.Prog`. -/
@[expose] def readDenseItemProg (U V w N d : ℕ) : BitMemory.Prog (ℕ × ℕ) := do
  let q ← BitMemory.readBits (itemQuotBitOff U V w N d) (quotientBits U N)
  let v ← BitMemory.readBits (itemValBitOff U V w N d) (valBits V)
  pure (q, v)

/-- Write `(q, v)` into dense item `d` in `BitMemory.Prog`. -/
@[expose] def writeDenseItemProg (U V w N d q v : ℕ) : BitMemory.Prog Unit := do
  BitMemory.writeBits (itemQuotBitOff U V w N d) (quotientBits U N) q
  BitMemory.writeBits (itemValBitOff U V w N d) (valBits V) v

/-- Deterministic post-state of `appendDenseItemProg` under `BitMemory.spec w`. -/
@[expose] def appendDenseItemState (U V w N q v : ℕ) (s : BitMemory.State) : BitMemory.State :=
  (BitMemory.spec w).clientState s (appendDenseItemProg U V N q v)

theorem appendDenseItemState_eq (U V w N q v : ℕ) (s : BitMemory.State) :
    appendDenseItemState U V w N q v s =
      let s_g1 := (BitMemory.stepFn w s (.grow (quotientBits U N))).1
      let s_w1 : BitMemory.State :=
        ⟨writeFieldMem w 0 s_g1.mem s.bitSize (quotientBits U N) q, s.bitSize + quotientBits U N⟩
      let s_g2 := (BitMemory.stepFn w s_w1 (.grow (valBits V))).1
      ⟨writeFieldMem w 0 s_g2.mem (s.bitSize + quotientBits U N) (valBits V) v,
        s.bitSize + quotientBits U N + valBits V⟩ := rfl

@[simp]
theorem appendDenseItemState_bitSize (U V w N q v : ℕ) (s : BitMemory.State) :
    (appendDenseItemState U V w N q v s).bitSize = s.bitSize + itemBits U V N := by
  rw [appendDenseItemState_eq]
  unfold itemBits
  dsimp only
  omega

/-- **Demonic determinism of `appendDenseItemProg` (`appendDenseItemProg_demonic`):**
under the demonic `BitMemory.dirtySpec w` specification (where each `grow` fills newly allocated
bits with arbitrary adversarial values), `appendDenseItemProg U V N q v` is admissible whenever
`U ≤ 2 ^ w`, `V ≤ 2 ^ w`, `q < 2 ^ quotientBits U N`, `v < 2 ^ valBits V`, and
`Fits w (s.bitSize + itemBits U V N)`, and **every** demonic execution trace produces the exact
same well-formed post-state `appendDenseItemState U V w N q v s`. -/
theorem appendDenseItemProg_demonic {U V w N q v : ℕ} {s : BitMemory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hs : s.WellFormed w)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v)
    (hfits : Fits w (s.bitSize + itemBits U V N)) :
    ∀ {s₁ : BitMemory.State},
      BitMemory.dirtyStep w s (.grow (quotientBits U N)) s₁ s.bitSize →
      let s₂ : BitMemory.State :=
        ⟨writeFieldMem w 0 s₁.mem s.bitSize (quotientBits U N) q, s₁.bitSize⟩
      ∀ {s₃ : BitMemory.State},
        BitMemory.dirtyStep w s₂ (.grow (valBits V)) s₃ s₂.bitSize →
        let s₄ : BitMemory.State :=
          ⟨writeFieldMem w 0 s₃.mem s₂.bitSize (valBits V) v, s₃.bitSize⟩
        s₄ = appendDenseItemState U V w N q v s ∧
        s₄.WellFormed w ∧
        s₄.bitSize = s.bitSize + itemBits U V N := by
  intro s₁ hs₁ s₂ s₃ hs₃ s₄
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hfits_q : Fits w (s.bitSize + quotientBits U N) := by
    refine Fits.of_le hfits ?_
    unfold itemBits
    omega
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (quotientBits U N)) hw hs hfits_q hs₁
  have hs₂_mem_eq :
      s₂.mem = writeFieldMem w 0 (BitMemory.stepFn w s (.grow (quotientBits U N))).1.mem
        s.bitSize (quotientBits U N) q :=
    (BitMemory.writeFieldMem_of_dirtyStep_grow hw hs hqw hs₁).trans
      (BitMemory.writeFieldMem_clearRangeMem_self hw hs hqw q).symm
  have hs₂_eq : s₂ =
      ⟨writeFieldMem w 0 (BitMemory.stepFn w s (.grow (quotientBits U N))).1.mem
        s.bitSize (quotientBits U N) q, s.bitSize + quotientBits U N⟩ := by
    ext idx
    · exact congrFun hs₂_mem_eq idx
    · exact hs₁.1
  have hs₂_wf : s₂.WellFormed w := by
    have hwf1 : (BitMemory.stepFn w s (.grow (quotientBits U N))).1.WellFormed w :=
      BitMemory.wellFormed_stepFn (o := .grow (quotientBits U N)) hw hs hfits_q
    exact hs₂_eq.symm ▸ BitMemory.wellFormed_stepFn
      (o := .writeBits s.bitSize (quotientBits U N) q) hw hwf1 ⟨hqw, le_rfl, hq⟩
  have hfits_v : Fits w (s₂.bitSize + valBits V) := by
    change Fits w (s₁.bitSize + valBits V)
    rw [hs₁.1]
    simpa [itemBits, Nat.add_assoc] using hfits
  have hs₃_wf : s₃.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (valBits V)) hw hs₂_wf hfits_v hs₃
  have hs₄_wf : s₄.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .writeBits s₂.bitSize (valBits V) v) hw hs₃_wf
      ⟨hvw, hs₃.1.symm.le, hv⟩
  have hs₄_mem_eq :
      s₄.mem = writeFieldMem w 0 (BitMemory.stepFn w s₂ (.grow (valBits V))).1.mem
        s₂.bitSize (valBits V) v :=
    (BitMemory.writeFieldMem_of_dirtyStep_grow hw hs₂_wf hvw hs₃).trans
      (BitMemory.writeFieldMem_clearRangeMem_self hw hs₂_wf hvw v).symm
  have hs₄_eq : s₄ = appendDenseItemState U V w N q v s := by
    ext idx
    · rw [hs₄_mem_eq, appendDenseItemState_eq]
      dsimp only
      have hs₂_sz : s₂.bitSize = s.bitSize + quotientBits U N := hs₁.1
      rw [← hs₂_eq, ← hs₂_sz]
    · change s₃.bitSize = (appendDenseItemState U V w N q v s).bitSize
      rw [hs₃.1, show s₂.bitSize = s.bitSize + quotientBits U N from hs₁.1,
        appendDenseItemState_bitSize]
      unfold itemBits
      omega
  exact ⟨hs₄_eq, hs₄_wf, by rw [hs₄_eq, appendDenseItemState_bitSize]⟩

/-- Reading the newly appended dense item `n_t` (where `s.bitSize = itemBitOff U V w N n_t`) from
`appendDenseItemState U V w N q v s` returns `(q, v)`, and all earlier dense items `d < n_t` and
metadata words `< epochMetaWords U w N` are preserved. -/
theorem denseQuotAt_ValAt_appendDenseItemState {U V w N n_t q v : ℕ} {s : BitMemory.State}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hs : s.WellFormed w) (hsz : s.bitSize = itemBitOff U V w N n_t)
    (hq : Fits (quotientBits U N) q) (hv : Fits (valBits V) v)
    (hfits : Fits w (s.bitSize + itemBits U V N)) :
    let s' := appendDenseItemState U V w N q v s
    denseQuotAt U V w N s' n_t = q ∧
    denseValAt U V w N s' n_t = v ∧
    (∀ d < n_t, denseQuotAt U V w N s' d = denseQuotAt U V w N s d ∧
      denseValAt U V w N s' d = denseValAt U V w N s d) ∧
    (∀ a < epochMetaWords U w N, s'.mem a = s.mem a) := by
  intro s'
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hfits_q : Fits w (s.bitSize + quotientBits U N) := by
    refine Fits.of_le hfits ?_
    unfold itemBits
    omega
  set s_g1 := (BitMemory.stepFn w s (.grow (quotientBits U N))).1
  set s_w1 : BitMemory.State :=
    ⟨writeFieldMem w 0 s_g1.mem s.bitSize (quotientBits U N) q, s.bitSize + quotientBits U N⟩
  set s_g2 := (BitMemory.stepFn w s_w1 (.grow (valBits V))).1
  have hs'_eq : s' =
      ⟨writeFieldMem w 0 s_g2.mem (s.bitSize + quotientBits U N) (valBits V) v,
        s.bitSize + quotientBits U N + valBits V⟩ := rfl
  have hs_g1_mem : writeFieldMem w 0 s_g1.mem s.bitSize (quotientBits U N) q =
      writeFieldMem w 0 s.mem s.bitSize (quotientBits U N) q :=
    BitMemory.writeFieldMem_clearRangeMem_self hw hs hqw q
  have hs_w1_wf : s_w1.WellFormed w := by
    refine ⟨fun idx => ?_, hfits_q, fun i hi => ?_⟩
    · dsimp only [s_w1]
      rw [hs_g1_mem]
      exact writeFieldMem_fits hw hs.mem_fits hqw q idx
    · dsimp only [s_w1, BitMemory.State.getBit] at hi ⊢
      rw [hs_g1_mem, readBit_writeFieldMem hw s.mem hqw i]
      have hnot : ¬(s.bitSize ≤ i ∧ i < s.bitSize + quotientBits U N) := by omega
      rw [ite_eq_right hnot]
      exact hs.zero_above i (by omega)
  have hs_g2_mem :
      writeFieldMem w 0 s_g2.mem (s.bitSize + quotientBits U N) (valBits V) v =
        writeFieldMem w 0 s_w1.mem (s.bitSize + quotientBits U N) (valBits V) v :=
    BitMemory.writeFieldMem_clearRangeMem_self hw hs_w1_wf hvw v
  have hs'_mem :
      s'.mem =
        writeFieldMem w 0 (writeFieldMem w 0 s.mem s.bitSize (quotientBits U N) q)
          (s.bitSize + quotientBits U N) (valBits V) v := by
    change writeFieldMem w 0 s_g2.mem (s.bitSize + quotientBits U N) (valBits V) v = _
    rw [hs_g2_mem]
    dsimp only [s_w1]
    rw [hs_g1_mem]
  have hq_off : itemQuotBitOff U V w N n_t = s.bitSize := hsz.symm
  have hv_off : itemValBitOff U V w N n_t = s.bitSize + quotientBits U N := by
    unfold itemValBitOff
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold denseQuotAt BitMemory.State.getField
    rw [hs'_mem, hq_off,
      readField_writeFieldMem_of_disjoint hw _ hvw hqw (Or.inl le_rfl),
      readField_writeFieldMem_same hw _ hqw hq]
  · unfold denseValAt BitMemory.State.getField
    rw [hs'_mem, hv_off, readField_writeFieldMem_same hw _ hvw hv]
  · intro d hd
    have hd_end : itemBitOff U V w N d + (quotientBits U N + valBits V) ≤ s.bitSize := by
      have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
      have h2 : itemBitOff U V w N d + itemBits U V N ≤ s.bitSize := by
        rw [hsz, ← itemBitOff_succ]
        unfold itemBitOff
        omega
      simpa only [itemBits] using h2
    have hq_disj1 :
        itemQuotBitOff U V w N d + quotientBits U N ≤ s.bitSize + quotientBits U N ∨
        (s.bitSize + quotientBits U N) + valBits V ≤ itemQuotBitOff U V w N d := by
      left; unfold itemQuotBitOff; omega
    have hq_disj2 :
        itemQuotBitOff U V w N d + quotientBits U N ≤ s.bitSize ∨
        s.bitSize + quotientBits U N ≤ itemQuotBitOff U V w N d := by
      left; unfold itemQuotBitOff; omega
    have hv_disj1 :
        itemValBitOff U V w N d + valBits V ≤ s.bitSize + quotientBits U N ∨
        (s.bitSize + quotientBits U N) + valBits V ≤ itemValBitOff U V w N d := by
      left; unfold itemValBitOff; omega
    have hv_disj2 :
        itemValBitOff U V w N d + valBits V ≤ s.bitSize ∨
        s.bitSize + quotientBits U N ≤ itemValBitOff U V w N d := by
      left; unfold itemValBitOff; omega
    refine ⟨?_, ?_⟩
    · unfold denseQuotAt BitMemory.State.getField
      rw [hs'_mem,
        readField_writeFieldMem_of_disjoint hw _ hvw hqw hq_disj1,
        readField_writeFieldMem_of_disjoint hw _ hqw hqw hq_disj2]
    · unfold denseValAt BitMemory.State.getField
      rw [hs'_mem,
        readField_writeFieldMem_of_disjoint hw _ hvw hvw hv_disj1,
        readField_writeFieldMem_of_disjoint hw _ hqw hvw hv_disj2]
  · intro a ha
    have ha_bits : (a + 1) * w ≤ s.bitSize := by
      rw [hsz]
      unfold itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    rw [hs'_mem]
    have h1 : writeFieldMem w 0 (writeFieldMem w 0 s.mem s.bitSize (quotientBits U N) q)
        (s.bitSize + quotientBits U N) (valBits V) v a =
        writeFieldMem w 0 s.mem s.bitSize (quotientBits U N) q a := by
      apply word_eq_of_readBit_eq hw
        (writeFieldMem_fits hw (writeFieldMem_fits hw hs.mem_fits hqw q) hvw v a)
        (writeFieldMem_fits hw hs.mem_fits hqw q a)
      intro j hj
      rw [readBit_writeFieldMem hw _ hvw (a * w + j)]
      have hnot : ¬(s.bitSize + quotientBits U N ≤ a * w + j ∧
          a * w + j < (s.bitSize + quotientBits U N) + valBits V) := by
        rw [Nat.add_one_mul] at ha_bits
        omega
      rw [ite_eq_right hnot]
    have h2 : writeFieldMem w 0 s.mem s.bitSize (quotientBits U N) q a = s.mem a := by
      apply word_eq_of_readBit_eq hw
        (writeFieldMem_fits hw hs.mem_fits hqw q a)
        (hs.mem_fits a)
      intro j hj
      rw [readBit_writeFieldMem hw _ hqw (a * w + j)]
      have hnot : ¬(s.bitSize ≤ a * w + j ∧ a * w + j < s.bitSize + quotientBits U N) := by
        rw [Nat.add_one_mul] at ha_bits
        omega
      rw [ite_eq_right hnot]
    rw [h1, h2]

/-- Predicate asserting that every register and every memory word of `x : BitRAM.Data r` fits in
`w` bits (`< 2 ^ w`). -/
@[expose] def RegsAndMemFit {r : ℕ} (w : ℕ) (x : BitRAM.Data r) : Prop :=
  (∀ i : Fin r, Fits w (x.regs i)) ∧ (∀ q : ℕ, Fits w (x.mem q))

theorem evalOp_preserve_regsAndMemFit {B : Basis} {r w : ℕ} {o : Cslib.WordRAM.Op B r}
    {x y : BitRAM.Data r} (hx : RegsAndMemFit w x) (heval : BitRAM.evalOp w o x = some y) :
    RegsAndMemFit w y := by
  cases o with
  | const d v =>
    dsimp only [BitRAM.evalOp, BitRAM.Data.put] at heval
    split_ifs at heval with hfit
    injection heval with hy
    subst hy
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hfit]
    · simp [BitRAM.Data.set, hi, hx.1 i]
  | copy d s =>
    dsimp only [BitRAM.evalOp] at heval
    injection heval with hy
    subst hy
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hx.1 s]
    · simp [BitRAM.Data.set, hi, hx.1 i]
  | alu f d args =>
    dsimp only [BitRAM.evalOp] at heval
    cases h : B.interp w f (x.regs ∘ args) with
    | none => simp [h] at heval
    | some val =>
      rw [h] at heval
      change x.put w d val = some y at heval
      dsimp only [BitRAM.Data.put] at heval
      split_ifs at heval with hfit
      injection heval with hy
      subst hy
      refine ⟨fun i => ?_, hx.2⟩
      by_cases hi : i = d
      · subst hi; simp [BitRAM.Data.set, hfit]
      · simp [BitRAM.Data.set, hi, hx.1 i]
  | load d a =>
    dsimp only [BitRAM.evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    refine ⟨fun i => ?_, hx.2⟩
    by_cases hi : i = d
    · subst hi; simp [BitRAM.Data.set, hx.2 (x.regs a)]
    · simp [BitRAM.Data.set, hi, hx.1 i]
  | store a s =>
    dsimp only [BitRAM.evalOp] at heval
    split_ifs at heval with hadm
    injection heval with hy
    subst hy
    refine ⟨hx.1, fun q => ?_⟩
    by_cases hq : q = x.regs a
    · subst hq; simp [BitRAM.Data.write, hx.1 s]
    · simp [BitRAM.Data.write, hq, hx.2 q]

/-- Every `DemonicExecWithin` derivation preserves `RegsAndMemFit w`. -/
theorem dExec_preserve_regsAndMemFit {B : Basis} {r w T : ℕ} {c : BitRAM.Code B r}
    {x : BitRAM.Data r} {P : BitRAM.Data r → Prop}
    (hx : RegsAndMemFit w x)
    (h : BitRAM.DemonicExecWithin w c x P T) :
    BitRAM.DemonicExecWithin w c x (fun y => P y ∧ RegsAndMemFit w y) T := by
  induction h with
  | op heval hp h1 =>
    exact .op heval ⟨hp, evalOp_preserve_regsAndMemFit hx heval⟩ h1
  | @grow dst δReg x P T hfits hcost hp =>
    refine .grow hfits hcost fun s' hs' => ⟨hp s' hs', ?_, hs'.2.2.1⟩
    intro i
    dsimp only
    by_cases hi : i = dst
    · subst hi
      rw [Function.update_self]
      exact Fits.of_le hfits (Nat.le_add_right _ _)
    · rw [Function.update_of_ne hi]
      exact hx.1 i
  | shrink hle hcost hp =>
    exact .shrink hle hcost ⟨hp, hx.1, fun q => BitMemory.clearRangeMem_fits w _ _ _ q⟩
  | @size dst x P T hfits hp h1 =>
    refine .size hfits ⟨hp, ?_, hx.2⟩ h1
    intro i
    by_cases hi : i = dst
    · subst hi; simp [BitRAM.Data.set, hfits]
    · simp [BitRAM.Data.set, hi, hx.1 i]
  | seq _ _ hsum ih₁ ih₂ =>
    exact .seq (ih₁ hx) (fun y ⟨hpy, hy_fit⟩ => ih₂ y hpy hy_fit) hsum
  | branch_pos hc _ hsum ih =>
    exact .branch_pos hc (ih hx) hsum
  | branch_neg hc _ hsum ih =>
    exact .branch_neg hc (ih hx) hsum

/-- Strengthened `writeBitsCode_exec` recording that the post-state `y` is well-formed
(`y.WellFormed w`). -/
theorem writeBitsCode_exec_wf {w : ℕ} (hw : 0 < w) {x : BitRAM.Data 12} (hx : x.WellFormed w)
    (hv : BitMemory.valid w x.toBitMemoryState (.writeBits (x.regs 1) (x.regs 2) (x.regs 3))) :
    BitRAM.DemonicExecWithin w BitRAM.writeBitsCode x
      (fun y =>
        y.toBitMemoryState =
          (BitMemory.stepFn w x.toBitMemoryState
            (.writeBits (x.regs 1) (x.regs 2) (x.regs 3))).1 ∧
        y.WellFormed w) 42 := by
  refine (dExec_preserve_regsAndMemFit ⟨hx.regs_fits, hx.mem_wf.mem_fits⟩
    (BitRAM.writeBitsCode_exec hw hx hv)).mono (fun y ⟨hst, hfit⟩ => ⟨hst, hfit.1, ?_⟩) le_rfl
  rw [hst]
  exact BitMemory.wellFormed_stepFn hw hx.mem_wf hv

/-- Concrete `BitRAM.Code .standard 12` program implementing `appendDenseItemProg U V N q v`:
1. Loads `quotientBits U N` into `r1`, runs `.grow 1 1` (putting old `bitSize` in `r1`), loads
   `q` into `r3`, loads `quotientBits U N` into `r2`, and runs `BitRAM.writeBitsCode`.
2. Loads `valBits V` into `r1`, runs `.grow 1 1` (putting `bitSize + quotientBits U N` in `r1`),
   loads `v` into `r3`, loads `valBits V` into `r2`, and runs `BitRAM.writeBitsCode`. -/
@[expose] def appendDenseItemCode (U V N q v : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 (quotientBits U N)))
    (.seq (.grow 1 1)
      (.seq (.op (.const 3 q))
        (.seq (.op (.const 2 (quotientBits U N)))
          (.seq BitRAM.writeBitsCode
            (.seq (.op (.const 1 (valBits V)))
              (.seq (.grow 1 1)
                (.seq (.op (.const 3 v))
                  (.seq (.op (.const 2 (valBits V)))
                    BitRAM.writeBitsCode))))))))

/-- **Machine-level demonic execution certificate for `appendDenseItemCode`:**
executes in at most `92` `BitRAM` instructions across all demonic `.grow` branches, producing the
exact deterministic post-state `appendDenseItemState U V w N q v x.toBitMemoryState`. -/
theorem appendDenseItemCode_exec {U V w N q v : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hq : Fits (quotientBits U N) q)
    (hv : Fits (valBits V) v)
    (hfits : Fits w (x.bitSize + itemBits U V N)) :
    BitRAM.DemonicExecWithin w (appendDenseItemCode U V N q v) x
      (fun y =>
        y.toBitMemoryState =
          appendDenseItemState U V w N q v x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.bitSize = x.bitSize + itemBits U V N) 92 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hq_val_fits : Fits w q := hq.mono hqw
  have hv_val_fits : Fits w v := hv.mono hvw
  have hgrow1_fits : Fits w (x.bitSize + quotientBits U N) := by
    refine Fits.of_le hfits ?_
    unfold itemBits
    omega
  have hcost1 : max 1 ((quotientBits U N) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hqw x.toBitMemoryState).le
  refine DemonicExecWithin.step_const (T := 91) hq_fits ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      ∃ s₁ : BitMemory.State,
        BitMemory.dirtyStep w x.toBitMemoryState (.grow (quotientBits U N)) s₁ x.bitSize ∧
        y₁ = ⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize,
          s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 90)
    (.grow hgrow1_fits hcost1 fun s₁ hs₁ => ⟨s₁, hs₁, rfl⟩)
    (fun y₁ ⟨s₁, hs₁, hy₁_eq⟩ => ?_) (by omega)
  subst hy₁_eq
  refine DemonicExecWithin.step_const (T := 89) hq_val_fits ?_
  refine DemonicExecWithin.step_const (T := 88) hq_fits ?_
  let x₂ : BitRAM.Data 12 :=
    ((⟨Function.update (x.set 1 (quotientBits U N)).regs 1 x.bitSize,
        s₁.mem, s₁.bitSize⟩ : BitRAM.Data 12).set 3 q).set 2 (quotientBits U N)
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (quotientBits U N)) hw hx.mem_wf hgrow1_fits hs₁
  have hx₂_wf : x₂.WellFormed w := by
    refine ⟨fun i => ?_, hs₁_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; exact hq_fits
    · by_cases hi3 : i = 3
      · subst hi3; exact hq_val_fits
      · by_cases hi1 : i = 1
        · subst hi1; exact hx.mem_wf.bitSize_fits
        · simp only [x₂, BitRAM.Data.set, Function.update_of_ne hi2,
            Function.update_of_ne hi3, Function.update_of_ne hi1]
          exact hx.regs_fits i
  have hv_write1 : BitMemory.valid w x₂.toBitMemoryState
      (.writeBits (x₂.regs 1) (x₂.regs 2) (x₂.regs 3)) := by
    refine ⟨hqw, ?_, hq⟩
    change x.bitSize + quotientBits U N ≤ s₁.bitSize
    exact hs₁.1.symm.le
  refine .seq (T₁ := 42) (T₂ := 46)
    (writeBitsCode_exec_wf hw hx₂_wf hv_write1)
    (fun y₂ ⟨hy₂_st, hy₂_wf⟩ => ?_) (by omega)
  change y₂.toBitMemoryState =
    ⟨writeFieldMem w 0 s₁.mem x.bitSize (quotientBits U N) q, s₁.bitSize⟩ at hy₂_st
  have hsz2 : y₂.bitSize = s₁.bitSize := congrArg BitMemory.State.bitSize hy₂_st
  have hgrow2_fits : Fits w (y₂.bitSize + valBits V) := by
    rw [hsz2, hs₁.1]
    change Fits w (x.bitSize + quotientBits U N + valBits V)
    simpa [itemBits, Nat.add_assoc] using hfits
  have hcost2 : max 1 ((valBits V) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_grow_of_le hw hvw y₂.toBitMemoryState).le
  refine DemonicExecWithin.step_const (T := 45) hv_fits ?_
  refine .seq
    (Q := fun y₃ : BitRAM.Data 12 =>
      ∃ s₃ : BitMemory.State,
        BitMemory.dirtyStep w y₂.toBitMemoryState (.grow (valBits V)) s₃ y₂.bitSize ∧
        y₃ = ⟨Function.update (y₂.set 1 (valBits V)).regs 1 y₂.bitSize,
          s₃.mem, s₃.bitSize⟩)
    (T₁ := 1) (T₂ := 44)
    (.grow hgrow2_fits hcost2 fun s₃ hs₃ => ⟨s₃, hs₃, rfl⟩)
    (fun y₃ ⟨s₃, hs₃, hy₃_eq⟩ => ?_) (by omega)
  subst hy₃_eq
  refine DemonicExecWithin.step_const (T := 43) hv_val_fits ?_
  refine DemonicExecWithin.step_const (T := 42) hv_fits ?_
  let x₄ : BitRAM.Data 12 :=
    ((⟨Function.update (y₂.set 1 (valBits V)).regs 1 y₂.bitSize,
        s₃.mem, s₃.bitSize⟩ : BitRAM.Data 12).set 3 v).set 2 (valBits V)
  have hs₃_wf : s₃.WellFormed w :=
    BitMemory.wellFormed_dirtyStep (o := .grow (valBits V)) hw hy₂_wf.mem_wf hgrow2_fits hs₃
  have hx₄_wf : x₄.WellFormed w := by
    refine ⟨fun i => ?_, hs₃_wf⟩
    by_cases hi2 : i = 2
    · subst hi2; exact hv_fits
    · by_cases hi3 : i = 3
      · subst hi3; exact hv_val_fits
      · by_cases hi1 : i = 1
        · subst hi1; exact hy₂_wf.mem_wf.bitSize_fits
        · simp only [x₄, BitRAM.Data.set, Function.update_of_ne hi2,
            Function.update_of_ne hi3, Function.update_of_ne hi1]
          exact hy₂_wf.regs_fits i
  have hv_write2 : BitMemory.valid w x₄.toBitMemoryState
      (.writeBits (x₄.regs 1) (x₄.regs 2) (x₄.regs 3)) := by
    refine ⟨hvw, ?_, hv⟩
    change y₂.bitSize + valBits V ≤ s₃.bitSize
    exact hs₃.1.symm.le
  refine (writeBitsCode_exec_wf hw hx₄_wf hv_write2).mono (fun y ⟨hy_st, hy_wf⟩ => ?_) le_rfl
  have hs₃' : BitMemory.dirtyStep w
      ⟨writeFieldMem w 0 s₁.mem x.toBitMemoryState.bitSize (quotientBits U N) q, s₁.bitSize⟩
      (.grow (valBits V)) s₃ s₁.bitSize := by
    change BitMemory.dirtyStep w
      ⟨writeFieldMem w 0 s₁.mem x.bitSize (quotientBits U N) q, s₁.bitSize⟩
      (.grow (valBits V)) s₃ s₁.bitSize
    rw [← hy₂_st, ← hsz2]
    exact hs₃
  have hdemonic :=
    appendDenseItemProg_demonic (s₁ := s₁) (s₃ := s₃) hw hU hV hx.mem_wf hq hv hfits hs₁ hs₃'
  have hy_st' : y.toBitMemoryState =
      ⟨writeFieldMem w 0 s₃.mem s₁.bitSize (valBits V) v, s₃.bitSize⟩ := by
    have : y.toBitMemoryState =
        ⟨writeFieldMem w 0 s₃.mem y₂.bitSize (valBits V) v, s₃.bitSize⟩ := hy_st
    rwa [hsz2] at this
  have hy_sz : y.bitSize = x.bitSize + itemBits U V N := by
    calc y.bitSize = y.toBitMemoryState.bitSize := rfl
      _ = s₃.bitSize := by rw [hy_st']
      _ = x.bitSize + itemBits U V N := hdemonic.2.2
  exact ⟨hy_st'.trans hdemonic.1, hy_wf, hy_sz⟩

/-- Strengthened `readBitsCode_exec` recording that the post-state `y` is well-formed
(`y.WellFormed w`). -/
theorem readBitsCode_exec_wf {w : ℕ} (hw : 0 < w) {x : BitRAM.Data 12} (hx : x.WellFormed w)
    (hv : BitMemory.valid w x.toBitMemoryState (.readBits (x.regs 1) (x.regs 2))) :
    BitRAM.DemonicExecWithin w BitRAM.readBitsCode x
      (fun y =>
        y.regs 0 = readField w 0 x.mem (x.regs 1) (x.regs 2) ∧
        y.toBitMemoryState = x.toBitMemoryState ∧
        y.WellFormed w) 32 := by
  refine (dExec_preserve_regsAndMemFit ⟨hx.regs_fits, hx.mem_wf.mem_fits⟩
    (BitRAM.readBitsCode_exec hw hx hv)).mono (fun y ⟨⟨hr0, hst⟩, hfit⟩ => ⟨hr0, hst, hfit.1, ?_⟩)
    le_rfl
  rw [hst]
  exact hx.mem_wf

/-- Deterministic `BitMemory.State` transformer popping one dense item of `itemBits U V N` bits
from the tail of `s` via two bit-level `.shrink` steps (`valBits V` then `quotientBits U N`). -/
@[expose] def popDenseItemState (U V w N : ℕ) (s : BitMemory.State) : BitMemory.State :=
  (BitMemory.stepFn w (BitMemory.stepFn w s (.shrink (valBits V))).1
    (.shrink (quotientBits U N))).1

/-- Concrete `BitRAM.Code .standard 12` program popping one dense item (`itemBits U V N` bits) from
the bit-resizable tail in 4 instructions. -/
@[expose] def popDenseItemCode (U V N : ℕ) : BitRAM.Code .standard 12 :=
  .seq (.op (.const 1 (valBits V)))
    (.seq (.shrink 1)
      (.seq (.op (.const 1 (quotientBits U N)))
        (.shrink 1)))

/-- **Machine-level execution certificate for `popDenseItemCode`:**
executes in at most `4` `BitRAM` instructions, shrinking `x.bitSize` by `itemBits U V N` bits,
preserving `WellFormed w`, and preserving all earlier dense items `d < n_t` and all metadata words
`a < epochMetaWords U w N`. -/
theorem popDenseItemCode_exec {U V w N n_t : ℕ} {x : BitRAM.Data 12}
    (hw : 0 < w) (hU : U ≤ 2 ^ w) (hV : V ≤ 2 ^ w)
    (hx : x.WellFormed w)
    (hsz : x.bitSize = itemBitOff U V w N (n_t + 1)) :
    BitRAM.DemonicExecWithin w (popDenseItemCode U V N) x
      (fun y =>
        y.toBitMemoryState = popDenseItemState U V w N x.toBitMemoryState ∧
        y.WellFormed w ∧
        y.bitSize = itemBitOff U V w N n_t ∧
        (∀ d < n_t,
          denseQuotAt U V w N y.toBitMemoryState d =
            denseQuotAt U V w N x.toBitMemoryState d ∧
          denseValAt U V w N y.toBitMemoryState d =
            denseValAt U V w N x.toBitMemoryState d) ∧
        (∀ a < epochMetaWords U w N, y.mem a = x.mem a)) 4 := by
  have hqw : quotientBits U N ≤ w := quotientBits_le_of_le_pow hU
  have hvw : valBits V ≤ w := valBits_le_of_le_pow hV
  have hq_fits : Fits w (quotientBits U N) := Fits.of_le (fits_self w) hqw
  have hv_fits : Fits w (valBits V) := Fits.of_le (fits_self w) hvw
  have hsz_split : x.bitSize = itemBitOff U V w N n_t + quotientBits U N + valBits V := by
    rw [hsz, itemBitOff_succ]
    unfold itemBits
    omega
  have hv_le : valBits V ≤ x.bitSize := by omega
  have hcost1 : max 1 ((valBits V) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hvw x.toBitMemoryState).le
  set s₁ := (BitMemory.stepFn w x.toBitMemoryState (.shrink (valBits V))).1
  have hs₁_wf : s₁.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (valBits V)) hw hx.mem_wf hv_le
  have hs₁_sz : s₁.bitSize = itemBitOff U V w N n_t + quotientBits U N := by
    change x.bitSize - valBits V = _
    omega
  have hq_le : quotientBits U N ≤ s₁.bitSize := by omega
  have hcost2 : max 1 ((quotientBits U N) ⌈/⌉ w) ≤ 1 :=
    (BitMemory.charge_shrink_of_le hw hqw s₁).le
  set s₂ := (BitMemory.stepFn w s₁ (.shrink (quotientBits U N))).1
  have hs₂_wf : s₂.WellFormed w :=
    BitMemory.wellFormed_stepFn (o := .shrink (quotientBits U N)) hw hs₁_wf hq_le
  have hs₂_sz : s₂.bitSize = itemBitOff U V w N n_t := by
    change s₁.bitSize - quotientBits U N = _
    omega
  refine DemonicExecWithin.step_const (T := 3) hv_fits ?_
  refine .seq
    (Q := fun y₁ : BitRAM.Data 12 =>
      y₁ = ⟨(x.set 1 (valBits V)).regs, s₁.mem, s₁.bitSize⟩)
    (T₁ := 1) (T₂ := 2)
    (.shrink hv_le hcost1 rfl)
    (fun y₁ hy₁ => ?_) (by omega)
  subst hy₁
  refine DemonicExecWithin.step_const (T := 1) hq_fits ?_
  refine DemonicExecWithin.shrink hq_le hcost2 ?_
  have hy_wf : (⟨((⟨(x.set 1 (valBits V)).regs, s₁.mem, s₁.bitSize⟩ : BitRAM.Data 12).set
      1 (quotientBits U N)).regs, s₂.mem, s₂.bitSize⟩ : BitRAM.Data 12).WellFormed w := by
    refine ⟨fun i => ?_, hs₂_wf⟩
    by_cases hi1 : i = 1
    · subst hi1; exact hq_fits
    · simp only [BitRAM.Data.set, Function.update_of_ne hi1]
      exact hx.regs_fits i
  have hbit_eq : ∀ i < itemBitOff U V w N n_t, s₂.getBit w i = x.toBitMemoryState.getBit w i := by
    intro i hi
    have h2 : s₂.getBit w i = s₁.getBit w i :=
      BitMemory.getBit_stepFn_shrink_of_lt hw s₁ (quotientBits U N) (by omega)
    have h1 : s₁.getBit w i = x.toBitMemoryState.getBit w i :=
      BitMemory.getBit_stepFn_shrink_of_lt hw x.toBitMemoryState (valBits V)
        (by change i < x.bitSize - valBits V; omega)
    rw [h2, h1]
  refine ⟨rfl, hy_wf, hs₂_sz, ?_, ?_⟩
  · intro d hd
    have hd_end : itemBitOff U V w N d + (quotientBits U N + valBits V) ≤
        itemBitOff U V w N n_t := by
      have h1 : (d + 1) * itemBits U V N ≤ n_t * itemBits U V N := Nat.mul_le_mul_right _ hd
      have h2 : itemBitOff U V w N d + itemBits U V N ≤ itemBitOff U V w N n_t := by
        rw [← itemBitOff_succ]
        unfold itemBitOff
        omega
      simpa only [itemBits] using h2
    refine ⟨?_, ?_⟩
    · unfold denseQuotAt
      have h2 := BitMemory.getField_stepFn_shrink (a := itemQuotBitOff U V w N d)
        hw s₁ (quotientBits U N) hqw (by unfold itemQuotBitOff; omega)
      have h1 := BitMemory.getField_stepFn_shrink (a := itemQuotBitOff U V w N d)
        hw x.toBitMemoryState (valBits V) hqw
        (by change itemQuotBitOff U V w N d + quotientBits U N ≤ x.bitSize - valBits V;
            unfold itemQuotBitOff; omega)
      exact h2.trans h1
    · unfold denseValAt
      have h2 := BitMemory.getField_stepFn_shrink (a := itemValBitOff U V w N d)
        hw s₁ (quotientBits U N) hvw (by unfold itemValBitOff; omega)
      have h1 := BitMemory.getField_stepFn_shrink (a := itemValBitOff U V w N d)
        hw x.toBitMemoryState (valBits V) hvw
        (by change itemValBitOff U V w N d + valBits V ≤ x.bitSize - valBits V;
            unfold itemValBitOff; omega)
      exact h2.trans h1
  · intro a ha
    have ha_bits : (a + 1) * w ≤ itemBitOff U V w N n_t := by
      unfold itemBitOff epochMetaBits
      have : (a + 1) * w ≤ epochMetaWords U w N * w := Nat.mul_le_mul_right w ha
      omega
    apply word_eq_of_readBit_eq hw (hs₂_wf.mem_fits a) (hx.mem_wf.mem_fits a)
    intro j hj
    have hi : a * w + j < itemBitOff U V w N n_t := by
      rw [Nat.add_one_mul] at ha_bits
      omega
    exact hbit_eq (a * w + j) hi

end Cslib.DataStructure.Dictionary.BitResizable
