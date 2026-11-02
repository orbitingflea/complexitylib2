/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.WordRAM.Defs
public import Complexity.Foundations.Data.Nat.Bitwise.Packing

/-!
# Sub-word bit-slice packing across word boundaries

This module provides the bit-packing operations and algebraic identities needed to store an array
of `b`-bit items (`b ≤ w`) tightly inside `w`-bit machine words (`⌈n * b / w⌉` words for `n`
items), where an item at bit offset `[i * b, (i + 1) * b)` may either lie within a single word
`(i * b) / w` or straddle the boundary between `(i * b) / w` and `(i * b) / w + 1`.

## Main definitions

* `Cslib.BitString.packedWords`: number of `w`-bit words `⌈n * b / w⌉ = (n * b + w - 1) / w`
  occupied by `n` items of width `b` bits.
* `Cslib.BitString.extractSlice`, `Cslib.BitString.spliceWord`: single-word bit-slice extraction
  and replacement.
* `Cslib.BitString.memBit`: bit-stream view of word-addressed memory `mem : ℕ → ℕ`.
* `Cslib.BitString.readSubword`, `Cslib.BitString.writeSubword`: reading and writing a `b`-bit
  item at index `i` using at most two word accesses.

## Main results

* `Cslib.BitString.mul_le_packedWords_mul`, `Cslib.BitString.packedWords_mul_le`,
  `Cslib.BitString.packedWords_succ_le`: tight word-count and bit-space inequalities.
* `Cslib.BitString.readSubword_eq_ofBits`: `readSubword` reconstructs the `b` bits starting at
  bit offset `i * b`.
* `Cslib.BitString.memBit_writeSubword`: `writeSubword` updates bits `[i * b, (i + 1) * b)` and
  preserves all other bits.
* `Cslib.BitString.readSubword_writeSubword_self`,
  `Cslib.BitString.readSubword_writeSubword_of_ne`: exact read-over-write laws for packed items.
-/

@[expose] public section

namespace Cslib.BitString

open Cslib.WordRAM

/-! ## Word count `⌈n * b / w⌉` and tight bit-space bounds -/

/-- Number of `w`-bit words `⌈n * b / w⌉ = (n * b + w - 1) / w` required to store `n` items of `b`
bits each. -/
def packedWords (w b n : ℕ) : ℕ :=
  (n * b + w - 1) / w

/-- Zero items require zero words. -/
@[simp]
theorem packedWords_zero (w b : ℕ) : packedWords w b 0 = 0 := by
  simp only [packedWords, Nat.zero_mul, Nat.zero_add]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rfl
  · exact Nat.div_eq_of_lt (by omega)

/-- Zero-width items require zero words. -/
@[simp]
theorem packedWords_zero_bits (w n : ℕ) : packedWords w 0 n = 0 := by
  simp only [packedWords, Nat.mul_zero, Nat.zero_add]
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rfl
  · exact Nat.div_eq_of_lt (by omega)

/-- The allocated words `packedWords w b n` provide at least `n * b` bits. -/
theorem mul_le_packedWords_mul {w b n : ℕ} (hw : 0 < w) :
    n * b ≤ packedWords w b n * w := by
  unfold packedWords
  have hdiv := Nat.div_add_mod (n * b + w - 1) w
  rw [Nat.mul_comm] at hdiv
  have hmod : (n * b + w - 1) % w < w := Nat.mod_lt _ hw
  omega

/-- The allocated words `packedWords w b n` use at most `n * b + (w - 1)` bits (less than one word
of rounding overhead). -/
theorem packedWords_mul_le {w b n : ℕ} :
    packedWords w b n * w ≤ n * b + (w - 1) := by
  unfold packedWords
  have hle := Nat.div_mul_le_self (n * b + w - 1) w
  omega

/-- `packedWords w b` is monotone in the item count `n`. -/
theorem packedWords_mono {w b m n : ℕ} (h : m ≤ n) :
    packedWords w b m ≤ packedWords w b n := by
  unfold packedWords
  exact Nat.div_le_div_right
    (Nat.sub_le_sub_right (Nat.add_le_add_right (Nat.mul_le_mul_right b h) w) 1)

/-- When `b ≤ w`, appending one `b`-bit item increases `packedWords w b n` by at most `1` word. -/
theorem packedWords_succ_le {w b n : ℕ} (hb : b ≤ w) :
    packedWords w b (n + 1) ≤ packedWords w b n + 1 := by
  unfold packedWords
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · simp
  · have hle : (n + 1) * b + w - 1 ≤ (n * b + w - 1) + w := by
      rw [Nat.succ_mul]
      omega
    calc
      ((n + 1) * b + w - 1) / w ≤ ((n * b + w - 1) + w) / w := Nat.div_le_div_right hle
      _ = (n * b + w - 1) / w + 1 := Nat.add_div_right _ hw

/-- Every bit position `i * b + k` (`i < n`, `k < b`) lies in a word strictly below
`packedWords w b n`. -/
theorem wordIdx_lt_packedWords {w b n i k : ℕ} (hw : 0 < w) (hi : i < n) (hk : k < b) :
    (i * b + k) / w < packedWords w b n := by
  rw [Nat.div_lt_iff_lt_mul hw]
  have hle : (i + 1) * b ≤ n * b := Nat.mul_le_mul_right b hi
  rw [Nat.add_mul, Nat.one_mul] at hle
  have h1 : i * b + k < n * b := by omega
  exact lt_of_lt_of_le h1 (mul_le_packedWords_mul hw)

/-- The starting word `(i * b) / w` of item `i < n` (when `0 < b`) is strictly less than
`packedWords w b n`. -/
theorem wordIdx_lt_packedWords_of_pos {w b n i : ℕ} (hw : 0 < w) (hb : 0 < b) (hi : i < n) :
    (i * b) / w < packedWords w b n := by
  simpa using wordIdx_lt_packedWords hw hi hb

/-- Subadditivity of `packedWords` up to at most 1 word of alignment rounding: packing `n₀` items
and `n₁` items into separate word-aligned arrays uses at most `packedWords w b (n₀ + n₁) + 1`
words in total. -/
theorem packedWords_add_le {w b n₀ n₁ : ℕ} (hw : 0 < w) :
    packedWords w b n₀ + packedWords w b n₁ ≤ packedWords w b (n₀ + n₁) + 1 := by
  have h0 : packedWords w b n₀ * w ≤ n₀ * b + (w - 1) := packedWords_mul_le
  have h1 : packedWords w b n₁ * w ≤ n₁ * b + (w - 1) := packedWords_mul_le
  have hsum : (n₀ + n₁) * b ≤ packedWords w b (n₀ + n₁) * w := mul_le_packedWords_mul hw
  have hmul : (packedWords w b n₀ + packedWords w b n₁) * w <
      (packedWords w b (n₀ + n₁) + 2) * w := by
    rw [Nat.add_mul] at hsum
    rw [Nat.add_mul, Nat.add_mul]
    omega
  have hlt : packedWords w b n₀ + packedWords w b n₁ < packedWords w b (n₀ + n₁) + 2 :=
    Nat.lt_of_mul_lt_mul_right hmul
  omega

/-! ## Single-word bit-slice extraction and splicing -/

/-- Extract `len` bits starting at bit offset `off` from `word`. -/
def extractSlice (word off len : ℕ) : ℕ :=
  (word / 2 ^ off) % 2 ^ len

/-- An extracted slice of width `len` fits in `len` bits. -/
theorem extractSlice_fits (word off len : ℕ) : Fits len (extractSlice word off len) :=
  Nat.mod_lt _ (Nat.two_pow_pos len)

/-- Bit `k` of `extractSlice word off len` is `word.testBit (off + k)` for `k < len` and `false`
otherwise. -/
theorem testBit_extractSlice (word off len k : ℕ) :
    (extractSlice word off len).testBit k = (decide (k < len) && word.testBit (off + k)) := by
  simp only [extractSlice, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow, Nat.add_comm off k]

/-- Replace bits `[off, off + len)` of a `w`-bit word `word` with the low `len` bits of `val`,
clipping the result to `w` bits. -/
def spliceWord (w word off len val : ℕ) : ℕ :=
  Nat.ofBits fun k : Fin w =>
    if off ≤ k.val ∧ k.val < off + len then val.testBit (k.val - off) else word.testBit k.val

/-- `spliceWord` always produces a `w`-bit word. -/
theorem spliceWord_fits (w word off len val : ℕ) : Fits w (spliceWord w word off len val) :=
  Nat.ofBits_lt_two_pow _

/-- Bit `k < w` of `spliceWord w word off len val`. -/
theorem testBit_spliceWord_of_lt {w word off len val k : ℕ} (hk : k < w) :
    (spliceWord w word off len val).testBit k =
      if off ≤ k ∧ k < off + len then val.testBit (k - off) else word.testBit k := by
  simpa only [spliceWord] using Nat.testBit_ofBits_lt _ k hk

/-- Bit `k ≥ w` of `spliceWord w word off len val` is `false`. -/
theorem testBit_spliceWord_of_ge {w word off len val k : ℕ} (hk : w ≤ k) :
    (spliceWord w word off len val).testBit k = false := by
  simpa only [spliceWord] using Nat.testBit_ofBits_ge _ k hk

/-! ## Sub-word array reads and writes across at most two consecutive words -/

/-- Bit `bitIdx` of word-addressed memory `mem : ℕ → ℕ` at word width `w`. -/
def memBit (w : ℕ) (mem : ℕ → ℕ) (bitIdx : ℕ) : Bool :=
  (mem (bitIdx / w)).testBit (bitIdx % w)

/-- Combine a low bit-slice of width `lowLen` and a high bit-slice of width `b - lowLen` into a
`b`-bit word. -/
def combineSlices (b lowLen lowPart highPart : ℕ) : ℕ :=
  spliceWord b lowPart lowLen (b - lowLen) highPart

/-- Read the `b`-bit item at index `i` from `mem` (at most two word reads when `b ≤ w`). -/
def readSubword (w : ℕ) (mem : ℕ → ℕ) (b i : ℕ) : ℕ :=
  let bitOff := i * b
  let wordIdx := bitOff / w
  let inWordOff := bitOff % w
  if inWordOff + b ≤ w then
    extractSlice (mem wordIdx) inWordOff b
  else
    let lowLen := w - inWordOff
    let highLen := b - lowLen
    combineSlices b lowLen
      (extractSlice (mem wordIdx) inWordOff lowLen)
      (extractSlice (mem (wordIdx + 1)) 0 highLen)

/-- Write the `b`-bit item `val` at index `i` in `mem` (at most two word reads and two word writes
when `b ≤ w`). -/
def writeSubword (w : ℕ) (mem : ℕ → ℕ) (b i val : ℕ) : ℕ → ℕ :=
  let bitOff := i * b
  let wordIdx := bitOff / w
  let inWordOff := bitOff % w
  if inWordOff + b ≤ w then
    Function.update mem wordIdx (spliceWord w (mem wordIdx) inWordOff b val)
  else
    let lowLen := w - inWordOff
    let highLen := b - lowLen
    let mem1 := Function.update mem wordIdx (spliceWord w (mem wordIdx) inWordOff lowLen val)
    Function.update mem1 (wordIdx + 1)
      (spliceWord w (mem1 (wordIdx + 1)) 0 highLen (val / 2 ^ lowLen))

/-- `readSubword` always returns a `b`-bit value (`Fits b`). -/
theorem readSubword_fits (w : ℕ) (mem : ℕ → ℕ) (b i : ℕ) :
    Fits b (readSubword w mem b i) := by
  dsimp only [readSubword]
  split_ifs
  · exact extractSlice_fits _ _ _
  · exact spliceWord_fits _ _ _ _ _

private theorem div_mod_of_inWord_lt {w bitOff k : ℕ} (hw : 0 < w)
    (hk : bitOff % w + k < w) :
    (bitOff + k) / w = bitOff / w ∧ (bitOff + k) % w = bitOff % w + k := by
  have hdecomp : bitOff + k = (bitOff % w + k) + w * (bitOff / w) := by
    have := Nat.div_add_mod bitOff w
    omega
  constructor
  · rw [hdecomp, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hk, Nat.zero_add]
  · rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]

private theorem div_mod_of_inWord_ge {w bitOff k : ℕ} (hw : 0 < w)
    (hge : w ≤ bitOff % w + k) (hlt : bitOff % w + k < 2 * w) :
    (bitOff + k) / w = bitOff / w + 1 ∧ (bitOff + k) % w = bitOff % w + k - w := by
  have hrem_lt : bitOff % w + k - w < w := by omega
  have hdecomp : bitOff + k = (bitOff % w + k - w) + w * (bitOff / w + 1) := by
    have := Nat.div_add_mod bitOff w
    rw [Nat.mul_add, Nat.mul_one]
    omega
  constructor
  · rw [hdecomp, Nat.add_mul_div_left _ _ hw, Nat.div_eq_of_lt hrem_lt, Nat.zero_add]
  · rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]

/-- When item `i < n` straddles a word boundary (`¬ ((i * b) % w + b ≤ w)`), the second word
`(i * b) / w + 1` is also strictly less than `packedWords w b n`. -/
theorem wordIdx_succ_lt_packedWords {w b n i : ℕ} (hw : 0 < w) (hi : i < n)
    (hsplit : ¬ ((i * b) % w + b ≤ w)) :
    (i * b) / w + 1 < packedWords w b n := by
  have hmod : (i * b) % w < w := Nat.mod_lt _ hw
  have hk : w - (i * b) % w < b := by omega
  have hdiv : (i * b + (w - (i * b) % w)) / w = (i * b) / w + 1 :=
    (div_mod_of_inWord_ge hw (by omega) (by omega)).1
  rw [← hdiv]
  exact wordIdx_lt_packedWords hw hi hk

/-- Bit `k < b` of `readSubword w mem b i` is `memBit w mem (i * b + k)`. -/
theorem testBit_readSubword_of_lt {w : ℕ} (mem : ℕ → ℕ) {b i k : ℕ}
    (hw : 0 < w) (hb : b ≤ w) (hk : k < b) :
    (readSubword w mem b i).testBit k = memBit w mem (i * b + k) := by
  dsimp only [readSubword, memBit]
  have hmod : (i * b) % w < w := Nat.mod_lt _ hw
  split_ifs with hfit
  · obtain ⟨hdiv, hrem⟩ := div_mod_of_inWord_lt hw (by omega : (i * b) % w + k < w)
    rw [testBit_extractSlice, decide_eq_true hk, Bool.true_and, hdiv, hrem]
  · unfold combineSlices
    rw [testBit_spliceWord_of_lt hk]
    by_cases hlow : k < w - (i * b) % w
    · have hcond : ¬ (w - (i * b) % w ≤ k ∧ k < w - (i * b) % w + (b - (w - (i * b) % w))) := by
        omega
      obtain ⟨hdiv, hrem⟩ := div_mod_of_inWord_lt hw (by omega : (i * b) % w + k < w)
      simp only [hcond, ↓reduceIte, testBit_extractSlice, decide_eq_true hlow, Bool.true_and,
        hdiv, hrem]
    · have hcond : w - (i * b) % w ≤ k ∧ k < w - (i * b) % w + (b - (w - (i * b) % w)) := by
        omega
      have hge : w ≤ (i * b) % w + k := by omega
      have hlt2 : (i * b) % w + k < 2 * w := by omega
      obtain ⟨hdiv, hrem⟩ := div_mod_of_inWord_ge hw hge hlt2
      have hk_sub : k - (w - (i * b) % w) < b - (w - (i * b) % w) := by omega
      have hsub_eq : k - (w - (i * b) % w) = (i * b) % w + k - w := by omega
      rw [ite_eq_left hcond, testBit_extractSlice, decide_eq_true hk_sub,
        Bool.true_and, Nat.zero_add, hdiv, hrem, hsub_eq]

/-- `readSubword` reconstructs the `b`-bit integer whose `k`-th bit is
`memBit w mem (i * b + k)`. -/
theorem readSubword_eq_ofBits {w : ℕ} (mem : ℕ → ℕ) {b i : ℕ}
    (hw : 0 < w) (hb : b ≤ w) :
    readSubword w mem b i = Nat.ofBits (fun k : Fin b => memBit w mem (i * b + k.val)) := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < b
  · rw [testBit_readSubword_of_lt mem hw hb hk, Nat.testBit_ofBits_lt _ k hk]
  · have h1 : (readSubword w mem b i).testBit k = false :=
      Nat.testBit_lt_two_pow
        ((readSubword_fits w mem b i).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [h1, Nat.testBit_ofBits_ge _ k (by omega)]

private theorem memBit_update_spliceWord {w : ℕ} (mem : ℕ → ℕ) {a off len val bitIdx : ℕ}
    (hw : 0 < w) (hfit : off + len ≤ w) :
    memBit w (Function.update mem a (spliceWord w (mem a) off len val)) bitIdx =
      if a * w + off ≤ bitIdx ∧ bitIdx < a * w + off + len then
        val.testBit (bitIdx - (a * w + off))
      else
        memBit w mem bitIdx := by
  unfold memBit
  have hbit_mod : bitIdx % w < w := Nat.mod_lt _ hw
  have hbit_eq : (bitIdx / w) * w + bitIdx % w = bitIdx := by
    have h := Nat.div_add_mod bitIdx w
    rw [Nat.mul_comm] at h
    exact h
  by_cases hdiv : bitIdx / w = a
  · rw [hdiv] at hbit_eq
    rw [hdiv, Function.update_self, testBit_spliceWord_of_lt hbit_mod]
    have hiff : (off ≤ bitIdx % w ∧ bitIdx % w < off + len) ↔
        (a * w + off ≤ bitIdx ∧ bitIdx < a * w + off + len) := by omega
    by_cases hrem : off ≤ bitIdx % w ∧ bitIdx % w < off + len
    · rw [ite_eq_left hrem, ite_eq_left (hiff.mp hrem)]
      congr 1
      omega
    · rw [ite_eq_right hrem, ite_eq_right (mt hiff.mpr hrem)]
  · rw [Function.update_of_ne hdiv]
    have hnot : ¬ (a * w + off ≤ bitIdx ∧ bitIdx < a * w + off + len) := by
      rcases lt_or_gt_of_ne hdiv with hlt | hgt
      · have hle : (bitIdx / w + 1) * w ≤ a * w := Nat.mul_le_mul_right w hlt
        rw [Nat.add_mul, Nat.one_mul] at hle
        omega
      · have hle : (a + 1) * w ≤ (bitIdx / w) * w := Nat.mul_le_mul_right w hgt
        rw [Nat.add_mul, Nat.one_mul] at hle
        omega
    rw [ite_eq_right hnot]

/-- `writeSubword` updates `memBit` on `[i * b, i * b + b)` to the bits of `val` and leaves all
other bit positions unchanged. -/
theorem memBit_writeSubword {w : ℕ} (mem : ℕ → ℕ) {b i val bitIdx : ℕ}
    (hw : 0 < w) (hb : b ≤ w) :
    memBit w (writeSubword w mem b i val) bitIdx =
      if i * b ≤ bitIdx ∧ bitIdx < i * b + b then val.testBit (bitIdx - i * b)
      else memBit w mem bitIdx := by
  dsimp only [writeSubword]
  have hmod : (i * b) % w < w := Nat.mod_lt _ hw
  have hib_eq : ((i * b) / w) * w + (i * b) % w = i * b := by
    have h := Nat.div_add_mod (i * b) w
    rw [Nat.mul_comm] at h
    exact h
  by_cases hfit : (i * b) % w + b ≤ w
  · rw [ite_eq_left hfit, memBit_update_spliceWord mem hw hfit]
    simp only [hib_eq]
  · rw [ite_eq_right hfit,
      memBit_update_spliceWord _ hw (by omega : 0 + (b - (w - (i * b) % w)) ≤ w),
      memBit_update_spliceWord mem hw (by omega : (i * b) % w + (w - (i * b) % w) ≤ w)]
    have hbase1 : ((i * b) / w + 1) * w + 0 = i * b + (w - (i * b) % w) := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    simp only [hbase1, hib_eq]
    by_cases hhi :
        i * b + (w - (i * b) % w) ≤ bitIdx ∧
          bitIdx < i * b + (w - (i * b) % w) + (b - (w - (i * b) % w))
    · have hfull : i * b ≤ bitIdx ∧ bitIdx < i * b + b := by omega
      rw [ite_eq_left hhi, ite_eq_left hfull, Nat.testBit_div_two_pow]
      congr 1
      omega
    · rw [ite_eq_right hhi]
      by_cases hlo : i * b ≤ bitIdx ∧ bitIdx < i * b + (w - (i * b) % w)
      · have hfull : i * b ≤ bitIdx ∧ bitIdx < i * b + b := by omega
        rw [ite_eq_left hlo, ite_eq_left hfull]
      · have hnot : ¬ (i * b ≤ bitIdx ∧ bitIdx < i * b + b) := by omega
        rw [ite_eq_right hlo, ite_eq_right hnot]

/-- Reading index `i` immediately after writing `val < 2 ^ b` to index `i` returns `val`. -/
@[simp]
theorem readSubword_writeSubword_self {w : ℕ} (mem : ℕ → ℕ) {b i val : ℕ}
    (hw : 0 < w) (hb : b ≤ w) (hval : Fits b val) :
    readSubword w (writeSubword w mem b i val) b i = val := by
  rw [readSubword_eq_ofBits _ hw hb]
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < b
  · rw [Nat.testBit_ofBits_lt _ k hk, memBit_writeSubword mem hw hb]
    have hrange : i * b ≤ i * b + k ∧ i * b + k < i * b + b := by omega
    simp only [hrange, and_self, ↓reduceIte, Nat.add_sub_cancel_left]
  · rw [Nat.testBit_ofBits_ge _ k (by omega)]
    exact (Nat.testBit_lt_two_pow
      (hval.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))).symm

/-- Reading index `j ≠ i` after writing to index `i` returns the prior value at index `j`. -/
theorem readSubword_writeSubword_of_ne {w : ℕ} (mem : ℕ → ℕ) {b i j val : ℕ}
    (hw : 0 < w) (hb : b ≤ w) (hne : j ≠ i) :
    readSubword w (writeSubword w mem b i val) b j = readSubword w mem b j := by
  rw [readSubword_eq_ofBits _ hw hb, readSubword_eq_ofBits _ hw hb]
  congr 1
  funext ⟨k, hk⟩
  rw [memBit_writeSubword mem hw hb]
  have hnot : ¬ (i * b ≤ j * b + k ∧ j * b + k < i * b + b) := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (j + 1) * b ≤ i * b := Nat.mul_le_mul_right b hlt
      rw [Nat.add_mul, Nat.one_mul] at hle
      omega
    · have hle : (i + 1) * b ≤ j * b := Nat.mul_le_mul_right b hgt
      rw [Nat.add_mul, Nat.one_mul] at hle
      omega
  rw [ite_eq_right hnot]

/-- `writeSubword` preserves word boundedness (`Fits w`). -/
theorem writeSubword_fits {w : ℕ} {mem : ℕ → ℕ} (hmem : ∀ a, Fits w (mem a))
    (b i val a : ℕ) : Fits w (writeSubword w mem b i val a) := by
  dsimp only [writeSubword]
  split_ifs
  · by_cases ha : a = (i * b) / w
    · subst ha; rw [Function.update_self]; exact spliceWord_fits _ _ _ _ _
    · rw [Function.update_of_ne ha]; exact hmem a
  · by_cases ha1 : a = (i * b) / w + 1
    · subst ha1; rw [Function.update_self]; exact spliceWord_fits _ _ _ _ _
    · rw [Function.update_of_ne ha1]
      by_cases ha0 : a = (i * b) / w
      · subst ha0; rw [Function.update_self]; exact spliceWord_fits _ _ _ _ _
      · rw [Function.update_of_ne ha0]; exact hmem a

/-- `writeSubword` leaves every word outside `{(i * b) / w, (i * b) / w + 1}` unchanged. -/
theorem writeSubword_eq_of_ne {w : ℕ} (mem : ℕ → ℕ) (b i val a : ℕ)
    (ha0 : a ≠ (i * b) / w) (ha1 : a ≠ (i * b) / w + 1) :
    writeSubword w mem b i val a = mem a := by
  dsimp only [writeSubword]
  split_ifs
  · exact Function.update_of_ne ha0 _ _
  · rw [Function.update_of_ne ha1, Function.update_of_ne ha0]

/-- If two memories agree on all words `< packedWords w b n`, then `readSubword` agrees on every
index `i < n`. -/
theorem readSubword_congr {w b n i : ℕ} {mem₁ mem₂ : ℕ → ℕ}
    (hw : 0 < w) (hb : b ≤ w) (hi : i < n)
    (hmem : ∀ a < packedWords w b n, mem₁ a = mem₂ a) :
    readSubword w mem₁ b i = readSubword w mem₂ b i := by
  rw [readSubword_eq_ofBits _ hw hb, readSubword_eq_ofBits _ hw hb]
  congr 1
  funext ⟨k, hk⟩
  unfold memBit
  rw [hmem _ (wordIdx_lt_packedWords hw hi hk)]

end Cslib.BitString
