/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.DataStructure.Memory.Spec
public import Complexity.DataStructure.Memory.Triple
public import Complexity.Foundations.Data.Nat.Bitwise.Packing
public import Complexity.Foundations.Data.Nat.CeilDiv

/-!
# Bit-Field Packing and Word-Boundary Plumbing over Word-Indexed Memory

In a bit-granular resizable Word RAM with word width `w`, a data structure's memory is addressed at
the bit level (`[0, bitSize)`) while the underlying machine stores `w`-bit words (`mem : ℕ → ℕ`).
A `b`-bit field (`b ≤ w`) at an arbitrary bit offset `a` need not be word-aligned: it either lies
entirely inside word `base + a / w` or straddles the boundary between words `base + a / w` and
`base + a / w + 1`.

This module defines all bit-field extraction, update, and masking operations directly in terms of
standard Word-RAM bitwise and shift operations (`<<<`, `>>>`, `-`, `&&&`, `|||`, `^^^`), proves
their pointwise `Nat.testBit` characterizations and algebraic read-over-write laws, and packages
them as `Memory.Prog` programs over `Memory.spec w`:

* `bitMask`, `sliceMask`, `clearMask`, `extractSlice`, `writeSlice`: primitive bitwise/shift
  building blocks operating on single `w`-bit words.
* `readBit`, `readField`: functional bit and `b`-bit field extraction from `mem : ℕ → ℕ` relative
  to a word base `base` at word width `w`.
* `writeFieldMem`: functional `b`-bit field update across the at-most-two words spanned by
  `[a, a + b)`.
* `maskWordBelow`: bitwise masking of trailing bits at or above `bitSize`.
* `readFieldProg`, `writeFieldProg`: `Memory.Prog` programs that read and write a `b`-bit field
  (`b ≤ w`) at bit offset `a` using at most two word reads (cost `≤ 2`) and at most two
  read-modify-write word pairs (cost `≤ 4`), respectively.

## Design choices

* **Direct bitwise/shift definitions (`<<<`, `>>>`, `-`, `&&&`, `|||`, `^^^`) with `Nat.testBit`
  algebraic laws:**
  We define `extractSlice`, `writeSlice`, `readField`, `writeFieldMem`, and `maskWordBelow`
  directly using the standard Word-RAM shift and bitwise operations rather than `Nat.ofBits`.
  This guarantees that every operation in the memory specification executes as an explicit
  constant-length sequence of Word-RAM ALU instructions (`Op.bin`), while the proved `Nat.testBit`
  characterizations (`readField_testBit`, `readBit_writeFieldMem`) isolate word-boundary case
  splits from client data structures.
  *Rejected alternative:* Defining `readField` and `writeFieldMem` via `Nat.ofBits`, which leaves
  a gap between the specification and the shift-and-mask instructions executed by the Word-RAM ALU.

## Main definitions

* `bitMask`, `sliceMask`, `clearMask`, `extractSlice`, `writeSlice`: word-level bitwise/shift
  slice primitives.
* `readBit`, `readField`: bit and bit-field extraction from word-indexed memory.
* `writeFieldMem`: bit-field update on word-indexed memory.
* `maskWordBelow`: zero out all bits at bit offsets `≥ bitSize` while preserving `[0, bitSize)`.
* `readFieldProg`, `writeFieldProg`: `Memory.Prog` programs for unaligned `b`-bit field access.

## Main results

* `extractSlice_testBit`, `writeSlice_testBit`: bitwise characterization of single-word slice
  operations.
* `readBit_writeFieldMem`: exact pointwise bit characterization after writing a `b`-bit field.
* `readField_writeFieldMem_same`: reading back a written `b`-bit field returns the written value.
* `readField_writeFieldMem_of_disjoint`: writing a `b`-bit field preserves all disjoint bit fields.
* `readFieldProg_triple`, `writeFieldProg_triple`: Hoare triples over `Memory.spec w`.

## References

* [T. Hagerup, *Sorting and Searching on the Word RAM*][Hagerup1998]
-/

@[expose] public section

namespace Cslib.DataStructure.Memory.BitPacking

open Cslib.WordRAM Cslib.DataStructure Cslib.DataStructure.Memory

/-! ## Word-level shift and mask primitives -/

/-- A low-order mask `(1 <<< len) - 1 = 2 ^ len - 1` of `len` set bits. -/
def bitMask (len : ℕ) : ℕ :=
  (1 <<< len) - 1

theorem bitMask_eq_two_pow_sub_one (len : ℕ) : bitMask len = 2 ^ len - 1 := by
  simp [bitMask, Nat.shiftLeft_eq]

theorem bitMask_lt (len : ℕ) : bitMask len < 2 ^ len := by
  rw [bitMask_eq_two_pow_sub_one]
  exact Nat.pred_lt (Nat.ne_of_gt (Nat.two_pow_pos len))

theorem bitMask_fits {w len : ℕ} (h : len ≤ w) : Fits w (bitMask len) :=
  lt_of_lt_of_le (bitMask_lt len) (Nat.pow_le_pow_right Nat.two_pos h)

@[simp]
theorem bitMask_zero : bitMask 0 = 0 := rfl

@[simp]
theorem bitMask_testBit (len j : ℕ) : (bitMask len).testBit j = decide (j < len) := by
  rw [bitMask_eq_two_pow_sub_one, Nat.testBit_two_pow_sub_one]

/-- A mask `bitMask len <<< lo` with `len` set bits at bit positions `[lo, lo + len)`. -/
def sliceMask (lo len : ℕ) : ℕ :=
  (bitMask len) <<< lo

theorem sliceMask_lt {w lo len : ℕ} (h : lo + len ≤ w) : sliceMask lo len < 2 ^ w := by
  have h1 : bitMask len * 2 ^ lo < 2 ^ len * 2 ^ lo :=
    Nat.mul_lt_mul_of_pos_right (bitMask_lt len) (Nat.two_pow_pos lo)
  rw [← Nat.pow_add, Nat.add_comm] at h1
  exact lt_of_lt_of_le (by simpa [sliceMask, Nat.shiftLeft_eq] using h1)
    (Nat.pow_le_pow_right Nat.two_pos h)

theorem sliceMask_fits {w lo len : ℕ} (h : lo + len ≤ w) : Fits w (sliceMask lo len) :=
  sliceMask_lt h

@[simp]
theorem sliceMask_testBit (lo len j : ℕ) :
    (sliceMask lo len).testBit j = decide (lo ≤ j ∧ j < lo + len) := by
  rw [sliceMask, Nat.testBit_shiftLeft, bitMask_testBit]
  by_cases hlo : lo ≤ j <;> by_cases hhi : j < lo + len
  · have hsub : j - lo < len := by omega
    simp [hlo, hhi, hsub]
  · have hsub : ¬(j - lo < len) := by omega
    simp [hlo, hhi, hsub]
  · simp [hlo, hhi]
  · simp [hlo, hhi]

/-- Clear the bits of `word` selected by `mask` using `word ^^^ (word &&& mask)`.
Unlike bitwise negation `~~~mask`, this never sets high bits outside `word` and requires only `.and`
and `.xor`. -/
def clearMask (word mask : ℕ) : ℕ :=
  word ^^^ (word &&& mask)

@[simp]
theorem clearMask_testBit (word mask j : ℕ) :
    (clearMask word mask).testBit j = (word.testBit j && !mask.testBit j) := by
  rw [clearMask, Nat.testBit_xor, Nat.testBit_and]
  cases word.testBit j <;> cases mask.testBit j <;> rfl

theorem clearMask_lt {w word : ℕ} (hword : word < 2 ^ w) (mask : ℕ) :
    clearMask word mask < 2 ^ w := by
  apply Nat.xor_lt_two_pow hword
  rw [Nat.and_comm]
  exact Nat.and_lt_two_pow mask hword

theorem clearMask_fits {w word : ℕ} (hword : Fits w word) (mask : ℕ) :
    Fits w (clearMask word mask) :=
  clearMask_lt hword mask

/-- Extract the `len`-bit slice at bit offset `lo` from `word` via `(word >>> lo) &&& bitMask len`.
-/
def extractSlice (word lo len : ℕ) : ℕ :=
  (word >>> lo) &&& bitMask len

theorem extractSlice_lt (word lo len : ℕ) : extractSlice word lo len < 2 ^ len :=
  Nat.and_lt_two_pow (word >>> lo) (bitMask_lt len)

theorem extractSlice_fits (word lo len : ℕ) : Fits len (extractSlice word lo len) :=
  extractSlice_lt word lo len

@[simp]
theorem extractSlice_zero (word lo : ℕ) : extractSlice word lo 0 = 0 := by
  simp [extractSlice]

@[simp]
theorem extractSlice_testBit (word lo len k : ℕ) :
    (extractSlice word lo len).testBit k = (decide (k < len) && word.testBit (lo + k)) := by
  rw [extractSlice, Nat.testBit_and, Nat.testBit_shiftRight, bitMask_testBit, Bool.and_comm,
    Nat.add_comm]

/-- When `word < 2 ^ w`, extracting all `w` bits from offset `0` equals `word` itself. -/
theorem extractSlice_zero_self {w word : ℕ} (hword : Fits w word) :
    extractSlice word 0 w = word := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [extractSlice_testBit, Nat.zero_add]
  by_cases hk : k < w
  · simp [hk]
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hword
      (Nat.pow_le_pow_right Nat.two_pos (Nat.le_of_not_lt hk)))).symm

/-- When `word < 2 ^ w` and `lo + len = w`, `extractSlice word lo len` equals `word >>> lo` without
requiring a `len`-bit mask. -/
theorem extractSlice_eq_shiftRight_of_add_eq {w word lo len : ℕ} (hword : Fits w word)
    (h : lo + len = w) :
    extractSlice word lo len = word >>> lo := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [extractSlice_testBit, Nat.testBit_shiftRight]
  by_cases hk : k < len
  · simp [hk]
  · simp only [hk, decide_false, Bool.false_and]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hword
      (Nat.pow_le_pow_right Nat.two_pos (by omega)))).symm

/-- Write the low `len` bits of `val` into bit positions `[lo, lo + len)` of `word`. -/
def writeSlice (word lo len val : ℕ) : ℕ :=
  clearMask word (sliceMask lo len) ||| ((val &&& bitMask len) <<< lo)

theorem writeSlice_lt {w word lo len val : ℕ} (hword : word < 2 ^ w) (hbound : lo + len ≤ w) :
    writeSlice word lo len val < 2 ^ w := by
  apply Nat.or_lt_two_pow (clearMask_lt hword _)
  have h1 : (val &&& bitMask len) * 2 ^ lo < 2 ^ len * 2 ^ lo :=
    Nat.mul_lt_mul_of_pos_right (Nat.and_lt_two_pow val (bitMask_lt len)) (Nat.two_pow_pos lo)
  rw [← Nat.pow_add, Nat.add_comm] at h1
  exact lt_of_lt_of_le (by simpa [Nat.shiftLeft_eq] using h1)
    (Nat.pow_le_pow_right Nat.two_pos hbound)

theorem writeSlice_fits {w word lo len val : ℕ} (hword : Fits w word) (hbound : lo + len ≤ w) :
    Fits w (writeSlice word lo len val) :=
  writeSlice_lt hword hbound

@[simp]
theorem writeSlice_testBit (word lo len val j : ℕ) :
    (writeSlice word lo len val).testBit j =
      if lo ≤ j ∧ j < lo + len then val.testBit (j - lo) else word.testBit j := by
  rw [writeSlice, Nat.testBit_or, clearMask_testBit, sliceMask_testBit,
    Nat.testBit_shiftLeft, Nat.testBit_and, bitMask_testBit]
  by_cases hlo : lo ≤ j
  · by_cases hhi : j < lo + len
    · have hlt : j - lo < len := by omega
      simp [hlo, hhi, hlt]
    · have hlt : ¬(j - lo < len) := by omega
      simp [hlo, hhi, hlt]
  · have hhi : ¬(lo ≤ j ∧ j < lo + len) := fun h => hlo h.1
    simp [hlo]

/-- Overwriting all `w` bits of a `w`-bit word `word < 2 ^ w` with `val < 2 ^ w` yields `val`. -/
theorem writeSlice_zero_self {w word val : ℕ} (hword : Fits w word) (hval : Fits w val) :
    writeSlice word 0 w val = val := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [writeSlice_testBit]
  by_cases hj : j < w
  · simp [hj]
  · have hnot : ¬(0 ≤ j ∧ j < 0 + w) := by omega
    rw [ite_eq_right hnot]
    have hle : w ≤ j := Nat.le_of_not_lt hj
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hword (Nat.pow_le_pow_right Nat.two_pos hle)),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hval (Nat.pow_le_pow_right Nat.two_pos hle))]

/-! ## Pointwise bit and bit-field extraction from word-indexed memory -/

/-- Read bit `i` from word-indexed memory `mem` starting at word `base`, with `w` bits per word. -/
def readBit (w base : ℕ) (mem : ℕ → ℕ) (i : ℕ) : Bool :=
  (mem (base + i / w)).testBit (i % w)

/-- Read a `b`-bit field starting at bit offset `a` relative to word `base` at word width `w`,
defined directly via word-level shift-and-mask slices (`extractSlice`, `<<<`, `|||`). -/
def readField (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) : ℕ :=
  if b = 0 then 0
  else
    let q₀ := a / w
    let lo := a % w
    if w - lo < b then
      let lowLen := w - lo
      let highLen := b - lowLen
      extractSlice (mem (base + q₀)) lo lowLen |||
        (extractSlice (mem (base + q₀ + 1)) 0 highLen <<< lowLen)
    else
      extractSlice (mem (base + q₀)) lo b

/-- A `b`-bit field read from memory always fits in `b` bits (`< 2 ^ b`). -/
theorem readField_lt (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) :
    readField w base mem a b < 2 ^ b := by
  unfold readField
  dsimp only
  split_ifs with hb hstrad
  · subst hb
    decide
  · have hlow : w - a % w ≤ b := Nat.le_of_lt hstrad
    have hsum : (b - (w - a % w)) + (w - a % w) = b := Nat.sub_add_cancel hlow
    apply Nat.or_lt_two_pow
    · exact lt_of_lt_of_le (extractSlice_lt _ _ _) (Nat.pow_le_pow_right Nat.two_pos hlow)
    · have h1 : extractSlice (mem (base + a / w + 1)) 0 (b - (w - a % w)) * 2 ^ (w - a % w) <
          2 ^ (b - (w - a % w)) * 2 ^ (w - a % w) :=
        Nat.mul_lt_mul_of_pos_right (extractSlice_lt _ _ _) (Nat.two_pow_pos _)
      rw [← Nat.pow_add, hsum] at h1
      simpa [Nat.shiftLeft_eq] using h1
  · exact extractSlice_lt _ _ _

/-- A `b`-bit field read from memory satisfies `Fits b`. -/
theorem readField_fits (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) :
    Fits b (readField w base mem a b) :=
  readField_lt w base mem a b

@[simp]
theorem readField_zero (w base : ℕ) (mem : ℕ → ℕ) (a : ℕ) :
    readField w base mem a 0 = 0 := by
  simp [readField]

/-- Bit `k` of `readField w base mem a b` (for `0 < w` and `b ≤ w`) is `readBit w base mem (a + k)`
for `k < b`, and `false` otherwise. -/
theorem readField_testBit {w : ℕ} (hw : 0 < w) (base : ℕ) (mem : ℕ → ℕ)
    {a b : ℕ} (hbw : b ≤ w) (k : ℕ) :
    (readField w base mem a b).testBit k =
      if k < b then readBit w base mem (a + k) else false := by
  unfold readField
  by_cases hb : b = 0
  · subst hb
    simp
  have hmod : a % w < w := Nat.mod_lt a hw
  have hdiv_mod : w * (a / w) + a % w = a := Nat.div_add_mod a w
  rw [ite_eq_right hb]
  dsimp only
  split_ifs with hstrad hk hk
  · rw [Nat.testBit_or, extractSlice_testBit, Nat.testBit_shiftLeft, extractSlice_testBit,
      Nat.zero_add]
    by_cases hk_low : k < w - a % w
    · have hnot_ge : ¬(w - a % w ≤ k) := by omega
      have hlt_ak : a % w + k < w := by omega
      have heq : a + k = w * (a / w) + (a % w + k) := by omega
      have hdiv : (a + k) / w = a / w := by
        rw [heq, Nat.mul_add_div hw, Nat.div_eq_of_lt hlt_ak, Nat.add_zero]
      have hrem : (a + k) % w = a % w + k := by
        rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_ak]
      simp [hk_low, hnot_ge, readBit, hdiv, hrem]
    · have hge : w - a % w ≤ k := Nat.le_of_not_lt hk_low
      have hsub_lt : k - (w - a % w) < b - (w - a % w) := by omega
      have heq_ak : a + k = w * (a / w + 1) + (k - (w - a % w)) := by
        rw [Nat.mul_add, Nat.mul_one]
        omega
      have hrem_lt : k - (w - a % w) < w := by omega
      have hdiv : (a + k) / w = a / w + 1 := by
        rw [heq_ak, Nat.mul_add_div hw, Nat.div_eq_of_lt hrem_lt, Nat.add_zero]
      have hrem : (a + k) % w = k - (w - a % w) := by
        rw [heq_ak, Nat.mul_add_mod, Nat.mod_eq_of_lt hrem_lt]
      simp [hk_low, hge, hsub_lt, readBit, hdiv, hrem, Nat.add_assoc]
  · rw [Nat.testBit_or, extractSlice_testBit, Nat.testBit_shiftLeft, extractSlice_testBit]
    have hnot_low : ¬(k < w - a % w) := by omega
    have hnot_high : ¬(k - (w - a % w) < b - (w - a % w)) := by omega
    simp [hnot_low, hnot_high]
  · rw [extractSlice_testBit]
    have hlt_ak : a % w + k < w := by omega
    have heq : a + k = w * (a / w) + (a % w + k) := by omega
    have hdiv : (a + k) / w = a / w := by
      rw [heq, Nat.mul_add_div hw, Nat.div_eq_of_lt hlt_ak, Nat.add_zero]
    have hrem : (a + k) % w = a % w + k := by
      rw [heq, Nat.mul_add_mod, Nat.mod_eq_of_lt hlt_ak]
    simp [hk, readBit, hdiv, hrem]
  · rw [extractSlice_testBit]
    simp [hk]

/-- `readField` depends only on the bits in `[a, a + b)`. -/
theorem readField_congr_bits {w base : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ} {a b : ℕ}
    (hbw : b ≤ w)
    (h : ∀ k < b, readBit w base mem₁ (a + k) = readBit w base mem₂ (a + k)) :
    readField w base mem₁ a b = readField w base mem₂ a b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [readField_testBit hw base mem₁ hbw k, readField_testBit hw base mem₂ hbw k]
  split_ifs with hk
  · exact h k hk
  · rfl

/-- `readField` depends only on the words `base + (a + k) / w` for `k < b`. -/
theorem readField_congr_words {w base : ℕ} (hw : 0 < w) {mem₁ mem₂ : ℕ → ℕ} {a b : ℕ}
    (hbw : b ≤ w)
    (h : ∀ k < b, mem₁ (base + (a + k) / w) = mem₂ (base + (a + k) / w)) :
    readField w base mem₁ a b = readField w base mem₂ a b :=
  readField_congr_bits hw hbw fun k hk => by simp only [readBit, h k hk]

/-! ## Bitwise bit-field update in word-indexed memory -/

/-- Functional update of a `b`-bit field at bit offset `a` (relative to `base`) in word-indexed
memory `mem`, defined directly via `writeSlice` and `>>>`. -/
def writeFieldMem (w base : ℕ) (mem : ℕ → ℕ) (a b val : ℕ) : ℕ → ℕ :=
  if b = 0 then mem
  else
    let q₀ := a / w
    let lo := a % w
    if w - lo < b then
      let lowLen := w - lo
      let highLen := b - lowLen
      let mem₁ := Function.update mem (base + q₀)
        (writeSlice (mem (base + q₀)) lo lowLen val)
      Function.update mem₁ (base + q₀ + 1)
        (writeSlice (mem₁ (base + q₀ + 1)) 0 highLen (val >>> lowLen))
    else
      Function.update mem (base + q₀)
        (writeSlice (mem (base + q₀)) lo b val)

@[simp]
theorem writeFieldMem_zero (w base : ℕ) (mem : ℕ → ℕ) (a val : ℕ) :
    writeFieldMem w base mem a 0 val = mem := by
  simp [writeFieldMem]

/-- A non-empty field of width `b ≤ w` spans at most two consecutive words:
`(a + b - 1) / w = a / w` or `(a + b - 1) / w = a / w + 1`. -/
theorem div_add_pred_eq_or_succ {w a b : ℕ} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w) :
    (a + b - 1) / w = a / w ∨ (a + b - 1) / w = a / w + 1 := by
  have h1 : a / w ≤ (a + b - 1) / w := Nat.div_le_div_right (by omega)
  have h2 : (a + b - 1) / w ≤ (a + w - 1) / w := Nat.div_le_div_right (by omega)
  have h3 : a + w - 1 = w * (a / w) + (a % w + w - 1) := by
    have := Nat.div_add_mod a w
    omega
  have h4 : (a + w - 1) / w ≤ a / w + 1 := by
    rw [h3, Nat.mul_add_div hw]
    have : a % w < w := Nat.mod_lt a hw
    have : (a % w + w - 1) / w ≤ 1 := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hw).mpr (by omega))
    omega
  omega

/-- For `0 < w` and `0 < b ≤ w`, the field `[a, a + b)` straddles two words (`w - a % w < b`) if
and only if `(a + b - 1) / w ≠ a / w` (in which case `(a + b - 1) / w = a / w + 1`). -/
theorem sub_mod_lt_iff_div_ne {w a b : ℕ} (hw : 0 < w) (hb : 0 < b) :
    w - a % w < b ↔ (a + b - 1) / w ≠ a / w := by
  have hmod : a % w < w := Nat.mod_lt a hw
  have hdiv_mod : w * (a / w) + a % w = a := Nat.div_add_mod a w
  constructor
  · intro hlt hq
    have hge : w * (a / w + 1) ≤ a + b - 1 := by
      rw [Nat.mul_add, Nat.mul_one]
      omega
    have hdiv_ge : a / w + 1 ≤ (a + b - 1) / w := by
      have := Nat.div_le_div_right (c := w) hge
      rwa [Nat.mul_div_right _ hw] at this
    omega
  · intro hne
    by_contra hge
    have hlt : a % w + b - 1 < w := by omega
    have heq : a + b - 1 = w * (a / w) + (a % w + b - 1) := by omega
    have hdiv : (a + b - 1) / w = a / w := by
      rw [heq, Nat.mul_add_div hw, Nat.div_eq_of_lt hlt, Nat.add_zero]
    exact hne hdiv

/-- Writing a `b`-bit field (`b ≤ w`) preserves all words outside
`{base + a / w, base + a / w + 1}`. -/
theorem writeFieldMem_eq_of_ne (w base : ℕ) (mem : ℕ → ℕ) (a b val addr : ℕ)
    (h₀ : addr ≠ base + a / w) (h₁ : addr ≠ base + a / w + 1) :
    writeFieldMem w base mem a b val addr = mem addr := by
  unfold writeFieldMem
  by_cases hb : b = 0
  · simp [hb]
  · rw [ite_eq_right hb]
    dsimp only
    split_ifs with hstrad
    · rw [Function.update_of_ne h₁, Function.update_of_ne h₀]
    · exact Function.update_of_ne h₀ _ _

/-- Writing a `b`-bit field (`b ≤ w`) at `0 < w` preserves `Fits w` on every word in memory. -/
theorem writeFieldMem_fits {w base : ℕ} (hw : 0 < w) {mem : ℕ → ℕ}
    (hmem : ∀ addr, Fits w (mem addr)) {a b : ℕ} (hbw : b ≤ w) (val addr : ℕ) :
    Fits w (writeFieldMem w base mem a b val addr) := by
  have hmod : a % w < w := Nat.mod_lt a hw
  unfold writeFieldMem
  by_cases hb : b = 0
  · simp [hb, hmem addr]
  · rw [ite_eq_right hb]
    dsimp only
    split_ifs with hstrad
    · by_cases h1 : addr = base + a / w + 1
      · subst h1
        rw [Function.update_self]
        have hmem₁ : Fits w (Function.update mem (base + a / w)
            (writeSlice (mem (base + a / w)) (a % w) (w - a % w) val) (base + a / w + 1)) := by
          rw [Function.update_of_ne (by omega)]
          exact hmem _
        exact writeSlice_fits hmem₁ (by omega)
      · rw [Function.update_of_ne h1]
        by_cases h0 : addr = base + a / w
        · subst h0
          rw [Function.update_self]
          exact writeSlice_fits (hmem _) (by omega)
        · rw [Function.update_of_ne h0]
          exact hmem addr
    · by_cases h0 : addr = base + a / w
      · subst h0
        rw [Function.update_self]
        exact writeSlice_fits (hmem _) (by omega)
      · rw [Function.update_of_ne h0]
        exact hmem addr

/-- **Fundamental bit-level characterization of `writeFieldMem`**: for `0 < w` and `b ≤ w`,
writing `val` to `[a, a + b)` sets bit `i` (relative to `base`) to `val.testBit (i - a)` for
`i ∈ [a, a + b)` and leaves bit `i` unchanged for `i ∉ [a, a + b)`. -/
theorem readBit_writeFieldMem {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {a b val : ℕ} (hbw : b ≤ w) (i : ℕ) :
    readBit w base (writeFieldMem w base mem a b val) i =
      if a ≤ i ∧ i < a + b then val.testBit (i - a) else readBit w base mem i := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · have hnot : ¬(a ≤ i ∧ i < a + 0) := by omega
    rw [writeFieldMem_zero, ite_eq_right hnot]
  have hmod_i : i % w < w := Nat.mod_lt i hw
  have hdiv_mod_i : w * (i / w) + i % w = i := Nat.div_add_mod i w
  have hmod_a : a % w < w := Nat.mod_lt a hw
  have hdiv_mod_a : w * (a / w) + a % w = a := Nat.div_add_mod a w
  unfold readBit writeFieldMem
  rw [ite_eq_right (by omega)]
  dsimp only
  by_cases hstrad : w - a % w < b
  · rw [ite_eq_left hstrad]
    by_cases hi1 : i / w = a / w + 1
    · have hne01 : base + a / w + 1 ≠ base + a / w := by omega
      have haddr1 : base + i / w = base + a / w + 1 := by omega
      rw [haddr1, Function.update_self, Function.update_of_ne hne01, writeSlice_testBit,
        Nat.testBit_shiftRight]
      have hi_eq : i = w * (a / w) + w + i % w := by
        have := hdiv_mod_i
        rw [hi1, Nat.mul_add, Nat.mul_one] at this
        omega
      by_cases hj : i % w < b - (w - a % w)
      · have hcond1 : 0 ≤ i % w ∧ i % w < 0 + (b - (w - a % w)) := ⟨Nat.zero_le _, by omega⟩
        have hcond2 : a ≤ i ∧ i < a + b := ⟨by omega, by omega⟩
        rw [ite_eq_left hcond1, ite_eq_left hcond2]
        congr 1
        omega
      · have hcond1 : ¬(0 ≤ i % w ∧ i % w < 0 + (b - (w - a % w))) := by omega
        have hcond2 : ¬(a ≤ i ∧ i < a + b) := by omega
        rw [ite_eq_right hcond1, ite_eq_right hcond2]
    · have hne1 : base + i / w ≠ base + a / w + 1 := by omega
      rw [Function.update_of_ne hne1]
      by_cases hi0 : i / w = a / w
      · have haddr0 : base + i / w = base + a / w := by omega
        rw [haddr0, Function.update_self, writeSlice_testBit]
        have hi_eq : i = w * (a / w) + i % w := by
          rw [← hi0]
          exact hdiv_mod_i.symm
        by_cases hj : a % w ≤ i % w
        · have hcond1 : a % w ≤ i % w ∧ i % w < a % w + (w - a % w) := ⟨hj, by omega⟩
          have hcond2 : a ≤ i ∧ i < a + b := ⟨by omega, by omega⟩
          rw [ite_eq_left hcond1, ite_eq_left hcond2]
          congr 1
          omega
        · have hcond1 : ¬(a % w ≤ i % w ∧ i % w < a % w + (w - a % w)) := by omega
          have hcond2 : ¬(a ≤ i ∧ i < a + b) := by omega
          rw [ite_eq_right hcond1, ite_eq_right hcond2]
      · have hne0 : base + i / w ≠ base + a / w := by omega
        rw [Function.update_of_ne hne0]
        have hnot : ¬(a ≤ i ∧ i < a + b) := by
          rintro ⟨hai, hib⟩
          have hle1 : a / w ≤ i / w := Nat.div_le_div_right hai
          have hle2 : i / w ≤ (a + b - 1) / w := Nat.div_le_div_right (by omega)
          rcases div_add_pred_eq_or_succ (a := a) hw hb hbw with h | h
          · exact hi0 (le_antisymm (h ▸ hle2) hle1)
          · have hle2' : i / w ≤ a / w + 1 := h ▸ hle2
            rcases Nat.eq_or_lt_of_le hle1 with h0 | hlt
            · exact hi0 h0.symm
            · exact hi1 (le_antisymm hle2' hlt)
        rw [ite_eq_right hnot]
  · rw [ite_eq_right hstrad]
    by_cases hi0 : i / w = a / w
    · have haddr0 : base + i / w = base + a / w := by omega
      rw [haddr0, Function.update_self, writeSlice_testBit]
      have hi_eq : i = w * (a / w) + i % w := by
        rw [← hi0]
        exact hdiv_mod_i.symm
      by_cases hj : a % w ≤ i % w ∧ i % w < a % w + b
      · have hcond2 : a ≤ i ∧ i < a + b := ⟨by omega, by omega⟩
        rw [ite_eq_left hj, ite_eq_left hcond2]
        congr 1
        omega
      · have hcond2 : ¬(a ≤ i ∧ i < a + b) := by omega
        rw [ite_eq_right hj, ite_eq_right hcond2]
    · have hne0 : base + i / w ≠ base + a / w := by omega
      rw [Function.update_of_ne hne0]
      have hnot : ¬(a ≤ i ∧ i < a + b) := by
        rintro ⟨hai, hib⟩
        have hle1 : a / w ≤ i / w := Nat.div_le_div_right hai
        have hle2 : i / w ≤ (a + b - 1) / w := Nat.div_le_div_right (by omega)
        have heq_div : (a + b - 1) / w = a / w := by
          by_contra hne
          exact hstrad ((sub_mod_lt_iff_div_ne hw hb).mpr hne)
        exact hi0 (le_antisymm (heq_div ▸ hle2) hle1)
      rw [ite_eq_right hnot]

/-- **Read-over-write (same field)**: reading back the `b`-bit field at `a` after writing
`val < 2 ^ b` returns `val`. -/
theorem readField_writeFieldMem_same {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {a b val : ℕ} (hbw : b ≤ w) (hval : Fits b val) :
    readField w base (writeFieldMem w base mem a b val) a b = val := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [readField_testBit hw base _ hbw k]
  by_cases hk : k < b
  · rw [ite_eq_left hk, readBit_writeFieldMem hw mem hbw (a + k),
      ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [ite_eq_right hk]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hval
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hk)))).symm

/-- **Read-over-write (disjoint fields)**: writing a `b`-bit field at `a` leaves any disjoint
`b'`-bit field (`b' ≤ w`) at `a'` unchanged. -/
theorem readField_writeFieldMem_of_disjoint {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {a b val a' b' : ℕ} (hbw : b ≤ w) (hb'w : b' ≤ w) (hdisj : a' + b' ≤ a ∨ a + b ≤ a') :
    readField w base (writeFieldMem w base mem a b val) a' b' =
      readField w base mem a' b' := by
  apply readField_congr_bits hw hb'w
  intro k hk
  rw [readBit_writeFieldMem hw mem hbw (a' + k), ite_eq_right]
  omega

/-! ## Clearing trailing bits above `bitSize` -/

/-- Clear all bits at or above bit offset `bitSize` (relative to `base`) in word `q` using a
single bitwise mask `oldWord &&& bitMask (min w (bitSize - q * w))`. -/
def maskWordBelow (w : ℕ) (oldWord : ℕ) (q bitSize : ℕ) : ℕ :=
  oldWord &&& bitMask (min w (bitSize - q * w))

theorem maskWordBelow_fits (w oldWord q bitSize : ℕ) :
    Fits w (maskWordBelow w oldWord q bitSize) :=
  Nat.and_lt_two_pow oldWord (bitMask_fits (Nat.min_le_left w _))

theorem maskWordBelow_testBit_of_lt {w oldWord q bitSize j : ℕ} (hj : j < w) :
    (maskWordBelow w oldWord q bitSize).testBit j =
      if q * w + j < bitSize then oldWord.testBit j else false := by
  rw [maskWordBelow, Nat.testBit_and, bitMask_testBit]
  by_cases hlt : q * w + j < bitSize
  · have hmin : j < min w (bitSize - q * w) := Nat.lt_min.mpr ⟨hj, by omega⟩
    simp [hlt, hmin]
  · have hmin : ¬(j < min w (bitSize - q * w)) := by
      rw [Nat.lt_min]
      omega
    simp [hlt, hmin]

/-- Zero out all bits in `[bitSize, bitSize + δ)`: this is `writeFieldMem w base mem bitSize δ 0`
when `δ ≤ w`. -/
theorem readBit_writeFieldMem_zero {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {bitSize δ : ℕ} (hδ : δ ≤ w) (i : ℕ) :
    readBit w base (writeFieldMem w base mem bitSize δ 0) i =
      if bitSize ≤ i ∧ i < bitSize + δ then false else readBit w base mem i := by
  rw [readBit_writeFieldMem hw mem hδ i]
  simp

/-! ## `Memory.Prog` programs for `b`-bit field read and write -/

/-- Read a `b`-bit field (`b ≤ w`) at bit offset `a` relative to `base` using at most 2 word reads
on `Memory.spec w`. -/
def readFieldProg (w base a b : ℕ) : Prog ℕ :=
  if b = 0 then
    pure 0
  else
    let q₀ := a / w
    let lo := a % w
    if w - lo < b then do
      let lowLen := w - lo
      let highLen := b - lowLen
      let w₀ ← Memory.read (base + q₀)
      let w₁ ← Memory.read (base + q₀ + 1)
      pure (extractSlice w₀ lo lowLen ||| (extractSlice w₁ 0 highLen <<< lowLen))
    else do
      let w₀ ← Memory.read (base + q₀)
      pure (extractSlice w₀ lo b)

/-- Write a `b`-bit field (`b ≤ w`) at bit offset `a` relative to `base` using at most 2 word reads
and 2 word writes (cost `≤ 4`) on `Memory.spec w`. -/
def writeFieldProg (w base a b val : ℕ) : Prog Unit :=
  if b = 0 then
    pure ()
  else
    let q₀ := a / w
    let lo := a % w
    if w - lo < b then do
      let lowLen := w - lo
      let highLen := b - lowLen
      let w₀ ← Memory.read (base + q₀)
      Memory.write (base + q₀) (writeSlice w₀ lo lowLen val)
      let w₁ ← Memory.read (base + q₀ + 1)
      Memory.write (base + q₀ + 1) (writeSlice w₁ 0 highLen (val >>> lowLen))
    else do
      let w₀ ← Memory.read (base + q₀)
      Memory.write (base + q₀) (writeSlice w₀ lo b val)

/-- If `a + b ≤ capWords * w` and `0 < b`, then both `a / w` and `(a + b - 1) / w` are strictly
below `capWords`. -/
theorem word_indices_lt_of_bit_bound {w a b capWords : ℕ} (hw : 0 < w) (hb : 0 < b)
    (hbound : a + b ≤ capWords * w) :
    a / w < capWords ∧ (a + b - 1) / w < capWords := by
  refine ⟨(Nat.div_lt_iff_lt_mul hw).mpr (by omega),
    (Nat.div_lt_iff_lt_mul hw).mpr (by omega)⟩

/-- **Hoare triple for `readFieldProg`**: reading a `b`-bit field (`b ≤ w`) at bit offset `a`
(where the spanned words are below `s.frontier`) costs at most 2 memory units, leaves the memory
state unchanged, and returns `readField w base s.mem a b`. -/
theorem readFieldProg_triple {w base a b : ℕ} (hw : 0 < w) (hbw : b ≤ w) {s : Memory.State}
    (hfront : b = 0 ∨ (base + a / w < s.frontier ∧ base + (a + b - 1) / w < s.frontier)) :
    Triple w s (readFieldProg w base a b) 2
      (fun r s' => r = readField w base s.mem a b ∧ s' = s) := by
  unfold readFieldProg readField
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact Triple.pure ⟨rfl, rfl⟩
  · rw [ite_eq_right hb, ite_eq_right hb]
    dsimp only
    rcases hfront with rfl | ⟨h₀, h₁⟩
    · exact absurd rfl hb
    · split_ifs with hstrad
      · have hpos : 0 < b := Nat.pos_of_ne_zero hb
        have hne := (sub_mod_lt_iff_div_ne hw hpos).mp hstrad
        have hq₁ : (a + b - 1) / w = a / w + 1 := by
          rcases div_add_pred_eq_or_succ hw hpos hbw with h | h
          · exact absurd h hne
          · exact h
        have h₁' : base + a / w + 1 < s.frontier := by omega
        exact Triple.read_bind (c := 1) h₀
          (Triple.read_bind (c := 0) h₁' (Triple.pure ⟨rfl, rfl⟩))
      · exact Triple.read_bind (c := 1) h₀ (Triple.pure ⟨rfl, rfl⟩)

/-- **Hoare triple for `writeFieldProg`**: writing a `b`-bit field (`b ≤ w`) at bit offset `a`
(where the spanned words are below `s.frontier` and `s` is well-formed at word width `w > 0`) costs
at most 4 memory units, preserves `s.frontier`, and updates `s.mem` to
`writeFieldMem w base s.mem a b val`. -/
theorem writeFieldProg_triple {w base a b val : ℕ} (hw : 0 < w) (hbw : b ≤ w) {s : Memory.State}
    (hmem : ∀ addr, Fits w (s.mem addr))
    (hfront : b = 0 ∨ (base + a / w < s.frontier ∧ base + (a + b - 1) / w < s.frontier)) :
    Triple w s (writeFieldProg w base a b val) 4
      (fun _ s' => s'.mem = writeFieldMem w base s.mem a b val ∧ s'.frontier = s.frontier) := by
  have hmod : a % w < w := Nat.mod_lt a hw
  unfold writeFieldProg writeFieldMem
  by_cases hb : b = 0
  · rw [ite_eq_left hb, ite_eq_left hb]
    exact Triple.pure ⟨rfl, rfl⟩
  · rw [ite_eq_right hb, ite_eq_right hb]
    dsimp only
    rcases hfront with rfl | ⟨h₀, h₁⟩
    · exact absurd rfl hb
    · split_ifs with hstrad
      · have hpos : 0 < b := Nat.pos_of_ne_zero hb
        have hne := (sub_mod_lt_iff_div_ne hw hpos).mp hstrad
        have hq₁ : (a + b - 1) / w = a / w + 1 := by
          rcases div_add_pred_eq_or_succ hw hpos hbw with h | h
          · exact absurd h hne
          · exact h
        have h₁' : base + a / w + 1 < s.frontier := by omega
        have hfits₀ : Fits w (writeSlice (s.mem (base + a / w)) (a % w) (w - a % w) val) :=
          writeSlice_fits (hmem _) (by omega)
        have hfits₁ : Fits w (writeSlice
            (Function.update s.mem (base + a / w)
              (writeSlice (s.mem (base + a / w)) (a % w) (w - a % w) val) (base + a / w + 1))
            0 (b - (w - a % w)) (val >>> (w - a % w))) := by
          rw [Function.update_of_ne (by omega)]
          exact writeSlice_fits (hmem _) (by omega)
        exact Triple.read_bind (c := 3) h₀
          (Triple.write_bind (c := 2) h₀ hfits₀
            (Triple.read_bind (c := 1) h₁'
              (Triple.write_bind (c := 0) h₁' hfits₁
                (Triple.pure ⟨rfl, rfl⟩))))
      · have hfits₀ : Fits w (writeSlice (s.mem (base + a / w)) (a % w) b val) :=
          writeSlice_fits (hmem _) (by omega)
        exact Triple.read_bind (c := 3) h₀
          (Triple.write_bind (c := 2) h₀ hfits₀
            (Triple.pure ⟨rfl, rfl⟩))

end Cslib.DataStructure.Memory.BitPacking
