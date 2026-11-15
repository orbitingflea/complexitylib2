/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Fixed-width packed `W`-bit word lanes

A natural-number word packs consecutive `W`-bit lanes in little-endian order, with lane `j`
extracted via `(word >>> (j * W)) &&& (2 ^ W - 1)` (`laneGet`). This module provides the shared
pure `Nat` bitwise/radix laws for `laneGet` used by packed SWAR search trees and character tries:
division-and-modulus and bit-level characterizations, lane extensionality, base-`2 ^ W` expansion
of bounded words (`word_eq_sum_laneGet`), and bounded-word digit injectivity
(`eq_of_forall_laneGet_eq_of_lt`). These are pure natural-number identities and make no machine
word-width or runtime claims.

## Main definitions

* `Cslib.DataStructure.laneGet`: extract the `W`-bit lane at index `j` from `word`.

## Main results

* `Cslib.DataStructure.laneGet_eq_div_mod`, `Cslib.DataStructure.laneGet_lt`,
  `Cslib.DataStructure.testBit_laneGet`: arithmetic, range, and bit characterizations of `laneGet`.
* `Cslib.DataStructure.laneGet_sum_mul_pow`, `Cslib.DataStructure.word_eq_sum_laneGet`: lane
  extraction of base-`2 ^ W` sums and base-`2 ^ W` expansion of bounded words.
* `Cslib.DataStructure.eq_of_forall_laneGet_eq`,
  `Cslib.DataStructure.eq_of_forall_laneGet_eq_of_lt`: unbounded and bounded-word lane
  extensionality.
-/

public section

namespace Cslib.DataStructure

open Finset
open scoped BigOperators

/-- Extract the `W`-bit lane at index `j` from `word`. -/
@[expose] def laneGet (W word j : ℕ) : ℕ :=
  (word >>> (j * W)) &&& (2 ^ W - 1)

/-- Division-and-modulus characterization of `laneGet`. -/
theorem laneGet_eq_div_mod (W word j : ℕ) :
    laneGet W word j = (word / 2 ^ (j * W)) % 2 ^ W := by
  unfold laneGet
  rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]

/-- Every extracted `W`-bit lane is strictly less than `2 ^ W`. -/
theorem laneGet_lt (W word j : ℕ) : laneGet W word j < 2 ^ W := by
  rw [laneGet_eq_div_mod]
  exact Nat.mod_lt _ (Nat.two_pow_pos W)

/-- Bit `b` of `laneGet W word j` is `word.testBit (j * W + b)` when `b < W`, and `false`
otherwise. -/
theorem testBit_laneGet (W word j b : ℕ) :
    (laneGet W word j).testBit b = (decide (b < W) && word.testBit (j * W + b)) := by
  unfold laneGet
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight, Bool.and_comm,
    Nat.add_comm (j * W) b]

/-- Two words are equal when all of their `W`-bit lanes (`0 < W`) agree. -/
theorem eq_of_forall_laneGet_eq {W a b : ℕ} (hW : 0 < W)
    (h : ∀ k, laneGet W a k = laneGet W b k) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro t
  have ht : t = (t / W) * W + t % W := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have hmod : t % W < W := Nat.mod_lt t hW
  have ha := testBit_laneGet W a (t / W) (t % W)
  have hb := testBit_laneGet W b (t / W) (t % W)
  rw [h (t / W)] at ha
  simp only [hmod, decide_true, Bool.true_and, ← ht] at ha hb
  exact ha.symm.trans hb

private theorem sum_mul_pow_lt {W n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ W) :
    ∑ j ∈ range n, f j * 2 ^ (j * W) < 2 ^ (n * W) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [sum_range_succ]
    have hm_lt := ih (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hfm : f m + 1 ≤ 2 ^ W := hf m (Nat.lt_succ_self m)
    calc ∑ j ∈ range m, f j * 2 ^ (j * W) + f m * 2 ^ (m * W)
        < 2 ^ (m * W) + f m * 2 ^ (m * W) := by omega
      _ = (f m + 1) * 2 ^ (m * W) := by ring
      _ ≤ 2 ^ W * 2 ^ (m * W) := Nat.mul_le_mul_right _ hfm
      _ = 2 ^ ((m + 1) * W) := by rw [← Nat.pow_add, Nat.add_mul, one_mul, Nat.add_comm]

/-- Extracting lane `k` from a sum of `n` bounded `W`-bit lanes recovers `f k` for `k < n` and `0`
otherwise. -/
theorem laneGet_sum_mul_pow {W n : ℕ} {f : ℕ → ℕ} (hf : ∀ j < n, f j < 2 ^ W) (k : ℕ) :
    laneGet W (∑ j ∈ range n, f j * 2 ^ (j * W)) k = if k < n then f k else 0 := by
  induction n with
  | zero =>
    simp [laneGet]
  | succ m ih =>
    rw [sum_range_succ]
    set S := ∑ j ∈ range m, f j * 2 ^ (j * W)
    have hS_lt : S < 2 ^ (m * W) := sum_mul_pow_lt (fun j hj => hf j (Nat.lt_succ_of_lt hj))
    have hfm_lt : f m < 2 ^ W := hf m (Nat.lt_succ_self m)
    have hor : S + f m * 2 ^ (m * W) = S ||| (f m <<< (m * W)) := by
      rw [← Nat.shiftLeft_eq, Nat.add_comm, Nat.shiftLeft_add_eq_or_of_lt hS_lt, Nat.or_comm]
    apply Nat.eq_of_testBit_eq
    intro b
    rw [hor, testBit_laneGet]
    by_cases hb : b < W
    · simp only [hb, decide_true, Bool.true_and, Nat.testBit_or, Nat.testBit_shiftLeft]
      rcases lt_trichotomy k m with hlt | rfl | hgt
      · have hk1 : k < m + 1 := by omega
        have hnge : ¬(m * W ≤ k * W + b) := by
          have : (k + 1) * W ≤ m * W := Nat.mul_le_mul_right W hlt
          rw [Nat.add_mul, one_mul] at this
          omega
        have hih := congrArg (fun x => x.testBit b)
          (ih (fun j hj => hf j (Nat.lt_succ_of_lt hj)))
        rw [testBit_laneGet] at hih
        simpa [hk1, hlt, hnge, hb] using hih
      · have hk1 : k < k + 1 := Nat.lt_succ_self k
        have hge : k * W ≤ k * W + b := Nat.le_add_right _ _
        have hS0 : S.testBit (k * W + b) = false :=
          Nat.testBit_lt_two_pow (hS_lt.trans_le (Nat.pow_le_pow_right (by decide) hge))
        simp [hk1, hge, hS0]
      · have hnk1 : ¬(k < m + 1) := by omega
        have hge1 : (m + 1) * W ≤ k * W + b := by
          have : (m + 1) * W ≤ k * W := Nat.mul_le_mul_right W hgt
          omega
        have hS0 : S.testBit (k * W + b) = false :=
          Nat.testBit_lt_two_pow (hS_lt.trans_le (Nat.pow_le_pow_right (by decide) (by
            have : m * W ≤ (m + 1) * W := Nat.mul_le_mul_right W (by omega)
            omega)))
        simp only [hnk1, ↓reduceIte, Nat.zero_testBit, hS0, Bool.false_or]
        by_cases hge : m * W ≤ k * W + b
        · simp only [hge, decide_true, Bool.true_and]
          refine Nat.testBit_lt_two_pow (hfm_lt.trans_le (Nat.pow_le_pow_right (by decide) ?_))
          have : (m + 1) * W = m * W + W := by ring
          omega
        · simp [hge]
    · simp only [hb, decide_false, Bool.false_and]
      split_ifs with hk1
      · symm
        exact Nat.testBit_lt_two_pow ((hf k hk1).trans_le
          (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hb)))
      · simp

/-- Base-`2 ^ W` expansion of any word `< 2 ^ (n * W)` into its first `n` lanes. -/
theorem word_eq_sum_laneGet {W n word : ℕ} (hW : 0 < W) (hw : word < 2 ^ (n * W)) :
    word = ∑ j ∈ range n, laneGet W word j * 2 ^ (j * W) := by
  refine eq_of_forall_laneGet_eq hW fun k => ?_
  rw [laneGet_sum_mul_pow (fun j _ => laneGet_lt W word j)]
  split_ifs with hk
  · rfl
  · apply Nat.eq_of_testBit_eq
    intro b
    rw [testBit_laneGet, Nat.zero_testBit]
    by_cases hb : b < W
    · simp only [hb, decide_true, Bool.true_and]
      refine Nat.testBit_lt_two_pow (hw.trans_le (Nat.pow_le_pow_right (by decide) ?_))
      have : n * W ≤ k * W := Nat.mul_le_mul_right W (Nat.le_of_not_lt hk)
      omega
    · simp [hb]

/-- Words `< 2 ^ (n * W)` are uniquely determined by their first `n` `W`-bit lanes. -/
theorem eq_of_forall_laneGet_eq_of_lt {n W a b : ℕ}
    (ha : a < 2 ^ (n * W)) (hb : b < 2 ^ (n * W))
    (hd : ∀ d < n, laneGet W a d = laneGet W b d) :
    a = b := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · simp at ha hb; omega
  · rw [word_eq_sum_laneGet hW ha, word_eq_sum_laneGet hW hb]
    exact Finset.sum_congr rfl fun d hd_mem => by rw [hd d (Finset.mem_range.mp hd_mem)]

end Cslib.DataStructure

end
