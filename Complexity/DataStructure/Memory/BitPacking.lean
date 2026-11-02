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

This module provides the bit-level read/write primitives on word-indexed memory and their
implementations as `Memory.Prog` programs over `Memory.spec w`:

* `readBit`, `readField`: functional bit and `b`-bit field extraction from `mem : ℕ → ℕ` relative
  to a word base `base` at word width `w`.
* `updateWordBits`, `writeFieldMem`: functional bit-field update in a single `w`-bit word and across
  the at-most-two words spanned by `[a, a + b)`.
* `readFieldProg`, `writeFieldProg`: `Memory.Prog` programs that read and write a `b`-bit field
  (`b ≤ w`) at bit offset `a` using at most two word reads (cost `≤ 2`) and at most two
  read-modify-write word pairs (cost `≤ 4`), respectively.

## Design choices

* **Canonical bit-level specification via `Nat.ofBits` and `Nat.testBit`:**
  We define `readField` and `updateWordBits` via `Nat.ofBits` and prove their shift/mask word
  identities alongside their pointwise `Nat.testBit` characterizations. This separates the
  algebraic bit-stream read-over-write laws (`readField_writeFieldMem_same`,
  `readField_writeFieldMem_of_disjoint`) from word-boundary case splits.
  *Rejected alternative:* Defining `readField` and `writeFieldMem` solely by nested division/modulo
  and conditional shift expressions without `Nat.ofBits`, which requires duplicating four-way
  single-word vs. two-word boundary case analysis in every client invariant proof.

## Main definitions

* `readBit`, `readField`: bit and bit-field extraction from word-indexed memory.
* `updateWordBits`, `writeFieldMem`: bit-field update on a single word and on word-indexed memory.
* `maskWordBelow`: zero out all bits at bit offsets `≥ bitSize` while preserving `[0, bitSize)`.
* `readFieldProg`, `writeFieldProg`: `Memory.Prog` programs for unaligned `b`-bit field access.

## Main results

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

/-! ## Pointwise bit and bit-field extraction -/

/-- Read bit `i` from word-indexed memory `mem` starting at word `base`, with `w` bits per word. -/
def readBit (w base : ℕ) (mem : ℕ → ℕ) (i : ℕ) : Bool :=
  (mem (base + i / w)).testBit (i % w)

/-- Read a `b`-bit field starting at bit offset `a` relative to word `base` at word width `w`. -/
def readField (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) : ℕ :=
  Nat.ofBits (fun k : Fin b => readBit w base mem (a + k.val))

/-- A `b`-bit field read from memory always fits in `b` bits (`< 2 ^ b`). -/
theorem readField_lt (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) :
    readField w base mem a b < 2 ^ b :=
  Nat.ofBits_lt_two_pow _

/-- A `b`-bit field read from memory satisfies `Fits b`. -/
theorem readField_fits (w base : ℕ) (mem : ℕ → ℕ) (a b : ℕ) :
    Fits b (readField w base mem a b) :=
  readField_lt w base mem a b

@[simp]
theorem readField_zero (w base : ℕ) (mem : ℕ → ℕ) (a : ℕ) :
    readField w base mem a 0 = 0 := by
  simp [readField]

/-- Bit `k` of `readField w base mem a b` is `readBit w base mem (a + k)` for `k < b`, and `false`
otherwise. -/
theorem readField_testBit (w base : ℕ) (mem : ℕ → ℕ) (a b k : ℕ) :
    (readField w base mem a b).testBit k =
      if k < b then readBit w base mem (a + k) else false := by
  by_cases hk : k < b
  · rw [ite_eq_left hk, readField, Nat.testBit_ofBits_lt _ _ hk]
  · rw [ite_eq_right hk, readField, Nat.testBit_ofBits_ge _ _ (Nat.le_of_not_lt hk)]

/-- `readField` depends only on the bits in `[a, a + b)`. -/
theorem readField_congr_bits {w base : ℕ} {mem₁ mem₂ : ℕ → ℕ} {a b : ℕ}
    (h : ∀ k < b, readBit w base mem₁ (a + k) = readBit w base mem₂ (a + k)) :
    readField w base mem₁ a b = readField w base mem₂ a b := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [readField_testBit, readField_testBit]
  split_ifs with hk
  · exact h k hk
  · rfl

/-- `readField` depends only on the words `base + (a + k) / w` for `k < b`. -/
theorem readField_congr_words {w base : ℕ} {mem₁ mem₂ : ℕ → ℕ} {a b : ℕ}
    (h : ∀ k < b, mem₁ (base + (a + k) / w) = mem₂ (base + (a + k) / w)) :
    readField w base mem₁ a b = readField w base mem₂ a b :=
  readField_congr_bits fun k hk => by simp only [readBit, h k hk]

/-! ## Pointwise bit-field update in word-indexed memory -/

/-- Update the bits of `oldWord` (word `q`, covering bit indices `[q * w, (q + 1) * w)`)
that fall within `[a, a + b)` to the corresponding bits of `val`. -/
def updateWordBits (w : ℕ) (oldWord : ℕ) (q a b val : ℕ) : ℕ :=
  Nat.ofBits (fun j : Fin w =>
    if a ≤ q * w + j.val ∧ q * w + j.val < a + b then
      val.testBit (q * w + j.val - a)
    else
      oldWord.testBit j.val)

/-- An updated word always fits in `w` bits (`< 2 ^ w`). -/
theorem updateWordBits_lt (w oldWord q a b val : ℕ) :
    updateWordBits w oldWord q a b val < 2 ^ w :=
  Nat.ofBits_lt_two_pow _

/-- An updated word satisfies `Fits w`. -/
theorem updateWordBits_fits (w oldWord q a b val : ℕ) :
    Fits w (updateWordBits w oldWord q a b val) :=
  updateWordBits_lt w oldWord q a b val

/-- Bit `j` of `updateWordBits` for `j < w`. -/
theorem updateWordBits_testBit_of_lt {w oldWord q a b val j : ℕ} (hj : j < w) :
    (updateWordBits w oldWord q a b val).testBit j =
      if a ≤ q * w + j ∧ q * w + j < a + b then
        val.testBit (q * w + j - a)
      else
        oldWord.testBit j := by
  simp [updateWordBits, Nat.testBit_ofBits_lt _ _ hj]

/-- If word `q` is disjoint from `[a, a + b)` and `oldWord < 2 ^ w`, `updateWordBits` leaves
`oldWord` unchanged. -/
theorem updateWordBits_eq_self {w oldWord q a b val : ℕ} (hold : oldWord < 2 ^ w)
    (hdisj : ∀ j < w, ¬(a ≤ q * w + j ∧ q * w + j < a + b)) :
    updateWordBits w oldWord q a b val = oldWord := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < w
  · rw [updateWordBits_testBit_of_lt hj, ite_eq_right (hdisj j hj)]
  · rw [updateWordBits, Nat.testBit_ofBits_ge _ _ (Nat.le_of_not_lt hj)]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hold
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hj)))).symm

/-- Functional update of a `b`-bit field at bit offset `a` (relative to `base`) in word-indexed
memory `mem`. When `0 < b`, this updates word `base + a / w` and (if `(a + b - 1) / w ≠ a / w`)
word `base + (a + b - 1) / w`. -/
def writeFieldMem (w base : ℕ) (mem : ℕ → ℕ) (a b val : ℕ) : ℕ → ℕ :=
  if b = 0 then mem
  else
    let q₀ := a / w
    let q₁ := (a + b - 1) / w
    let mem₁ := Function.update mem (base + q₀)
      (updateWordBits w (mem (base + q₀)) q₀ a b val)
    if q₁ = q₀ then mem₁
    else Function.update mem₁ (base + q₁)
      (updateWordBits w (mem₁ (base + q₁)) q₁ a b val)

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

/-- Any bit index `i ∈ [a, a + b)` for `b ≤ w` belongs to word `a / w` or word `(a + b - 1) / w`. -/
theorem div_eq_first_or_last {w a b i : ℕ} (hw : 0 < w) (hb : 0 < b) (hbw : b ≤ w)
    (hai : a ≤ i) (hib : i < a + b) :
    i / w = a / w ∨ i / w = (a + b - 1) / w := by
  have hle1 : a / w ≤ i / w := Nat.div_le_div_right hai
  have hle2 : i / w ≤ (a + b - 1) / w := Nat.div_le_div_right (by omega)
  rcases div_add_pred_eq_or_succ hw hb hbw with h | h
  · left
    rw [h] at hle2
    omega
  · by_cases h0 : i / w = a / w
    · exact Or.inl h0
    · right
      rw [h] at hle2 ⊢
      omega

/-- Writing a `b`-bit field (`b ≤ w`) preserves all words outside
`{base + a / w, base + (a + b - 1) / w}`. -/
theorem writeFieldMem_eq_of_ne (w base : ℕ) (mem : ℕ → ℕ) (a b val addr : ℕ)
    (h₀ : addr ≠ base + a / w) (h₁ : addr ≠ base + (a + b - 1) / w) :
    writeFieldMem w base mem a b val addr = mem addr := by
  unfold writeFieldMem
  by_cases hb : b = 0
  · simp [hb]
  · rw [ite_eq_right hb]
    by_cases hq : (a + b - 1) / w = a / w
    · rw [ite_eq_left hq]
      exact Function.update_of_ne h₀ _ _
    · rw [ite_eq_right hq, Function.update_of_ne h₁, Function.update_of_ne h₀]

/-- Writing a `b`-bit field preserves `Fits w` on every word in memory. -/
theorem writeFieldMem_fits {w base : ℕ} {mem : ℕ → ℕ} (hmem : ∀ addr, Fits w (mem addr))
    (a b val addr : ℕ) : Fits w (writeFieldMem w base mem a b val addr) := by
  unfold writeFieldMem
  by_cases hb : b = 0
  · simp [hb, hmem addr]
  · rw [ite_eq_right hb]
    by_cases hq : (a + b - 1) / w = a / w
    · rw [ite_eq_left hq]
      by_cases h : addr = base + a / w
      · subst h
        rw [Function.update_self]
        exact updateWordBits_fits _ _ _ _ _ _
      · rw [Function.update_of_ne h]
        exact hmem addr
    · rw [ite_eq_right hq]
      by_cases h1 : addr = base + (a + b - 1) / w
      · subst h1
        rw [Function.update_self]
        exact updateWordBits_fits _ _ _ _ _ _
      · rw [Function.update_of_ne h1]
        by_cases h0 : addr = base + a / w
        · subst h0
          rw [Function.update_self]
          exact updateWordBits_fits _ _ _ _ _ _
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
  have hmod : i % w < w := Nat.mod_lt i hw
  have hdiv_mod : i / w * w + i % w = i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i w
  unfold readBit writeFieldMem
  rw [ite_eq_right (by omega)]
  by_cases hq : (a + b - 1) / w = a / w
  · rw [ite_eq_left hq]
    by_cases hiw : i / w = a / w
    · rw [hiw, Function.update_self, updateWordBits_testBit_of_lt hmod]
      simp only [← hiw, hdiv_mod]
    · have hne : base + i / w ≠ base + a / w := by omega
      rw [Function.update_of_ne hne]
      have hnot : ¬(a ≤ i ∧ i < a + b) := by
        rintro ⟨hai, hib⟩
        rcases div_eq_first_or_last hw hb hbw hai hib with h | h
        · exact hiw h
        · exact hiw (h.trans hq)
      rw [ite_eq_right hnot]
  · rw [ite_eq_right hq]
    have hne_q : base + a / w ≠ base + (a + b - 1) / w := by omega
    by_cases hi1 : i / w = (a + b - 1) / w
    · rw [hi1, Function.update_self, Function.update_of_ne hne_q.symm,
        updateWordBits_testBit_of_lt hmod]
      simp only [← hi1, hdiv_mod]
    · have hne1 : base + i / w ≠ base + (a + b - 1) / w := by omega
      rw [Function.update_of_ne hne1]
      by_cases hi0 : i / w = a / w
      · rw [hi0, Function.update_self, updateWordBits_testBit_of_lt hmod]
        simp only [← hi0, hdiv_mod]
      · have hne0 : base + i / w ≠ base + a / w := by omega
        rw [Function.update_of_ne hne0]
        have hnot : ¬(a ≤ i ∧ i < a + b) := by
          rintro ⟨hai, hib⟩
          rcases div_eq_first_or_last hw hb hbw hai hib with h | h
          · exact hi0 h
          · exact hi1 h
        rw [ite_eq_right hnot]

/-- **Read-over-write (same field)**: reading back the `b`-bit field at `a` after writing
`val < 2 ^ b` returns `val`. -/
theorem readField_writeFieldMem_same {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {a b val : ℕ} (hbw : b ≤ w) (hval : Fits b val) :
    readField w base (writeFieldMem w base mem a b val) a b = val := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [readField_testBit]
  by_cases hk : k < b
  · rw [ite_eq_left hk, readBit_writeFieldMem hw mem hbw (a + k),
      ite_eq_left ⟨by omega, by omega⟩, Nat.add_sub_cancel_left]
  · rw [ite_eq_right hk]
    exact (Nat.testBit_lt_two_pow (lt_of_lt_of_le hval
      (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hk)))).symm

/-- **Read-over-write (disjoint fields)**: writing a `b`-bit field at `a` leaves any disjoint
`b'`-bit field at `a'` unchanged. -/
theorem readField_writeFieldMem_of_disjoint {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {a b val a' b' : ℕ} (hbw : b ≤ w) (hdisj : a' + b' ≤ a ∨ a + b ≤ a') :
    readField w base (writeFieldMem w base mem a b val) a' b' =
      readField w base mem a' b' := by
  apply readField_congr_bits
  intro k hk
  rw [readBit_writeFieldMem hw mem hbw (a' + k), ite_eq_right]
  omega

/-! ## Clearing trailing bits above `bitSize` -/

/-- Clear all bits at or above bit offset `bitSize` (relative to `base`) in word `q`. -/
def maskWordBelow (w : ℕ) (oldWord : ℕ) (q bitSize : ℕ) : ℕ :=
  Nat.ofBits (fun j : Fin w =>
    if q * w + j.val < bitSize then oldWord.testBit j.val else false)

theorem maskWordBelow_fits (w oldWord q bitSize : ℕ) :
    Fits w (maskWordBelow w oldWord q bitSize) :=
  Nat.ofBits_lt_two_pow _

theorem maskWordBelow_testBit_of_lt {w oldWord q bitSize j : ℕ} (hj : j < w) :
    (maskWordBelow w oldWord q bitSize).testBit j =
      if q * w + j < bitSize then oldWord.testBit j else false := by
  simp [maskWordBelow, Nat.testBit_ofBits_lt _ _ hj]

/-- Zero out all bits in `[bitSize, bitSize + δ)`: this is `writeFieldMem w base mem bitSize δ 0`
when `δ ≤ w`. -/
theorem readBit_writeFieldMem_zero {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ)
    {bitSize δ : ℕ} (hδ : δ ≤ w) (i : ℕ) :
    readBit w base (writeFieldMem w base mem bitSize δ 0) i =
      if bitSize ≤ i ∧ i < bitSize + δ then false else readBit w base mem i := by
  rw [readBit_writeFieldMem hw mem hδ i]
  simp

/-! ## `Memory.Prog` programs for `b`-bit field read and write -/

/-- Assemble a `b`-bit field from the single word `w₀` at `a / w`. -/
def assembleSingleWord (w a b w₀ : ℕ) : ℕ :=
  Nat.ofBits (fun k : Fin b => w₀.testBit ((a + k.val) % w))

/-- Assemble a `b`-bit field straddling `w₀` (at `a / w`) and `w₁` (at `(a + b - 1) / w`). -/
def assembleTwoWords (w a b w₀ w₁ : ℕ) : ℕ :=
  Nat.ofBits (fun k : Fin b =>
    if (a + k.val) / w = a / w then w₀.testBit ((a + k.val) % w)
    else w₁.testBit ((a + k.val) % w))

/-- Read a `b`-bit field (`b ≤ w`) at bit offset `a` relative to `base` using at most 2 word reads
on `Memory.spec w`. -/
def readFieldProg (w base a b : ℕ) : Prog ℕ :=
  if b = 0 then
    pure 0
  else if (a + b - 1) / w = a / w then do
    let w₀ ← Memory.read (base + a / w)
    pure (assembleSingleWord w a b w₀)
  else do
    let w₀ ← Memory.read (base + a / w)
    let w₁ ← Memory.read (base + (a + b - 1) / w)
    pure (assembleTwoWords w a b w₀ w₁)

/-- Write a `b`-bit field (`b ≤ w`) at bit offset `a` relative to `base` using at most 2 word reads
and 2 word writes (cost `≤ 4`) on `Memory.spec w`. -/
def writeFieldProg (w base a b val : ℕ) : Prog Unit :=
  if b = 0 then
    pure ()
  else
    let q₀ := a / w
    let q₁ := (a + b - 1) / w
    if q₁ = q₀ then do
      let w₀ ← Memory.read (base + q₀)
      Memory.write (base + q₀) (updateWordBits w w₀ q₀ a b val)
    else do
      let w₀ ← Memory.read (base + q₀)
      Memory.write (base + q₀) (updateWordBits w w₀ q₀ a b val)
      let w₁ ← Memory.read (base + q₁)
      Memory.write (base + q₁) (updateWordBits w w₁ q₁ a b val)

/-- If `a + b ≤ capWords * w` and `0 < b`, then both `a / w` and `(a + b - 1) / w` are strictly
below `capWords`. -/
theorem word_indices_lt_of_bit_bound {w a b capWords : ℕ} (hw : 0 < w) (hb : 0 < b)
    (hbound : a + b ≤ capWords * w) :
    a / w < capWords ∧ (a + b - 1) / w < capWords := by
  refine ⟨(Nat.div_lt_iff_lt_mul hw).mpr (by omega),
    (Nat.div_lt_iff_lt_mul hw).mpr (by omega)⟩

/-- `assembleSingleWord` agrees with `readField` when `(a + b - 1) / w = a / w`. -/
theorem assembleSingleWord_eq_readField {w base : ℕ} (mem : ℕ → ℕ) {a b : ℕ}
    (hq : (a + b - 1) / w = a / w) :
    assembleSingleWord w a b (mem (base + a / w)) = readField w base mem a b := by
  unfold assembleSingleWord readField readBit
  congr 1
  ext ⟨k, hk⟩
  have hle1 : a / w ≤ (a + k) / w := Nat.div_le_div_right (by omega)
  have hle2 : (a + k) / w ≤ (a + b - 1) / w := Nat.div_le_div_right (by omega)
  have heq : (a + k) / w = a / w := by omega
  rw [heq]

/-- `assembleTwoWords` agrees with `readField` when `b ≤ w` and `0 < b`. -/
theorem assembleTwoWords_eq_readField {w base : ℕ} (hw : 0 < w) (mem : ℕ → ℕ) {a b : ℕ}
    (hb : 0 < b) (hbw : b ≤ w) :
    assembleTwoWords w a b (mem (base + a / w)) (mem (base + (a + b - 1) / w)) =
      readField w base mem a b := by
  unfold assembleTwoWords readField readBit
  congr 1
  ext ⟨k, hk⟩
  rcases div_eq_first_or_last hw hb hbw (Nat.le_add_right a k) (by omega) with h | h
  · rw [ite_eq_left h, h]
  · by_cases h0 : (a + k) / w = a / w
    · rw [ite_eq_left h0, h0]
    · rw [ite_eq_right h0, h]

/-- **Hoare triple for `readFieldProg`**: reading a `b`-bit field (`b ≤ w`) at bit offset `a`
(where the spanned words are below `s.frontier`) costs at most 2 memory units, leaves the memory
state unchanged, and returns `readField w base s.mem a b`. -/
theorem readFieldProg_triple {w base a b : ℕ} (hw : 0 < w) (hbw : b ≤ w) {s : Memory.State}
    (hfront : b = 0 ∨ (base + a / w < s.frontier ∧ base + (a + b - 1) / w < s.frontier)) :
    Triple w s (readFieldProg w base a b) 2
      (fun r s' => r = readField w base s.mem a b ∧ s' = s) := by
  unfold readFieldProg
  split_ifs with hb hq
  · subst hb
    exact Triple.pure ⟨by simp, rfl⟩
  · rcases hfront with rfl | ⟨h₀, _⟩
    · exact absurd rfl hb
    · refine Triple.read_bind (c := 1) h₀ (Triple.pure ⟨?_, rfl⟩)
      exact assembleSingleWord_eq_readField s.mem hq
  · rcases hfront with rfl | ⟨h₀, h₁⟩
    · exact absurd rfl hb
    · refine Triple.read_bind (c := 1) h₀ (Triple.read_bind (c := 0) h₁ (Triple.pure ⟨?_, rfl⟩))
      exact assembleTwoWords_eq_readField hw s.mem (Nat.pos_of_ne_zero hb) hbw

/-- **Hoare triple for `writeFieldProg`**: writing a `b`-bit field (`b ≤ w`) at bit offset `a`
(where the spanned words are below `s.frontier`) costs at most 4 memory units, preserves
`s.frontier`, and updates `s.mem` to `writeFieldMem w base s.mem a b val`. -/
theorem writeFieldProg_triple {w base a b val : ℕ} {s : Memory.State}
    (hfront : b = 0 ∨ (base + a / w < s.frontier ∧ base + (a + b - 1) / w < s.frontier)) :
    Triple w s (writeFieldProg w base a b val) 4
      (fun _ s' => s'.mem = writeFieldMem w base s.mem a b val ∧ s'.frontier = s.frontier) := by
  unfold writeFieldProg
  by_cases hb : b = 0
  · rw [ite_eq_left hb]
    subst hb
    exact Triple.pure ⟨by simp, rfl⟩
  · rw [ite_eq_right hb]
    dsimp only
    rcases hfront with rfl | ⟨h₀, h₁⟩
    · exact absurd rfl hb
    · split_ifs with hq
      · refine Triple.read_bind (c := 3) h₀
          (Triple.write_bind (c := 2) h₀ (updateWordBits_fits w _ _ a b val)
            (Triple.pure ⟨?_, rfl⟩))
        simp [writeFieldMem, hb, hq]
      · refine Triple.read_bind (c := 3) h₀
          (Triple.write_bind (c := 2) h₀ (updateWordBits_fits w _ _ a b val)
            (Triple.read_bind (c := 1) h₁
              (Triple.write_bind (c := 0) h₁ (updateWordBits_fits w _ _ a b val)
                (Triple.pure ⟨?_, rfl⟩))))
        simp [writeFieldMem, hb, hq]

end Cslib.DataStructure.Memory.BitPacking
