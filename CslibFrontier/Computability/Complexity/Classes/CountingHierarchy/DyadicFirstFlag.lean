/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.FirstEventSign
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Foundations.NumberTheory.DoublingSign
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Classifying the first dyadic flag

`dyadicFirstFlagSign d B r N` classifies the first numerator in the flag window with margin
`1/d`, below the exclusive endpoint `r`. It returns one below one half, minus one above,
and zero when neither case occurs. This is a classifier of supplied dyadic values, not
sign recovery for an implicit integer. The operation is total for every natural parameter.

Binary polynomial-time margin denominator and endpoint, unary polynomial-time precision,
and a uniform F_a numerator evaluator give an F_(a+2) signed binary output. The semantic
bridge to `FirstCircleFlag` needs only `0 < d`, with no CRT or approximation assumption.

## Main definitions

* `Cslib.Complexity.dyadicFirstFlagSign`: total classifier at the first dyadic flag.

## Main results

* `Cslib.Complexity.CountingFunction.dyadicFirstFlagSign_mem`: the two-level bound.
* `Cslib.Complexity.dyadicFirstFlagSign_eq_one_iff`: the first flag is below one half.
* `Cslib.Complexity.dyadicFirstFlagSign_eq_neg_one_iff`: the first flag is above one half.
* `Cslib.Complexity.dyadicFirstFlagSign_eq_zero_iff`: neither strict side occurs.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Classify the first dyadic flag with margin denominator `d`, below `r`.
The classifier uses natural arithmetic only; no represented integer or CRT data is an input. -/
@[expose] noncomputable def dyadicFirstFlagSign (d B r : ℕ) (N : ℕ → ℕ) : ℤ :=
  firstEventSign
    (fun p : Unit × ℕ => decide (2 ^ B ≤ d * N p.2 ∧ d * N p.2 ≤ (d - 1) * 2 ^ B))
    (fun p => decide (2 * N p.2 < 2 ^ B))
    (fun p => decide (2 ^ B < 2 * N p.2)) (fun _ => r) ()

private theorem flag_iff {d B n : ℕ} (hd : 0 < d) :
    CircleFlag (1 / (d : ℚ)) ((n : ℚ) / (2 : ℚ) ^ B) ↔
      2 ^ B ≤ d * n ∧ d * n ≤ (d - 1) * 2 ^ B := by
  have hdq : (0 : ℚ) < d := by exact_mod_cast hd
  have hp : (0 : ℚ) < 2 ^ B := by positivity
  have hmargin : (1 : ℚ) - 1 / d = ((d - 1 : ℕ) : ℚ) / d := by
    rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one]
    field_simp
  rw [CircleFlag, hmargin, div_le_div_iff₀ hdq hp, div_le_div_iff₀ hp hdq]
  simp only [one_mul, mul_comm (n : ℚ) (d : ℚ)]
  norm_cast

private theorem left_iff (B n : ℕ) :
    (n : ℚ) / (2 : ℚ) ^ B < 1 / 2 ↔ 2 * n < 2 ^ B := by
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  simp only [one_mul, mul_comm (n : ℚ) 2]
  norm_cast

private theorem right_iff (B n : ℕ) :
    1 / 2 < (n : ℚ) / (2 : ℚ) ^ B ↔ 2 ^ B < 2 * n := by
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  simp only [one_mul, mul_comm (n : ℚ) 2]
  norm_cast

private theorem first_test_iff {d B r : ℕ} (hd : 0 < d) (N : ℕ → ℕ) (test : ℕ → Bool) :
    (∃ k < r, decide (2 ^ B ≤ d * N k ∧ d * N k ≤ (d - 1) * 2 ^ B) = true ∧
      test k = true ∧ ∀ j < k,
        decide (2 ^ B ≤ d * N j ∧ d * N j ≤ (d - 1) * 2 ^ B) = false) ↔
    ∃ k < r, FirstCircleFlag (1 / (d : ℚ)) (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k ∧
      test k = true := by
  simp only [decide_eq_true_eq, Bool.eq_false_iff]
  constructor
  · rintro ⟨k, hk, he, ht, hprev⟩
    refine ⟨k, hk, ⟨(flag_iff hd).mpr he, ?_⟩, ht⟩
    intro j hj hf
    exact hprev j hj (by simpa only [decide_eq_true_eq] using (flag_iff hd).mp hf)
  · rintro ⟨k, hk, ⟨hf, hprev⟩, ht⟩
    exact ⟨k, hk, (flag_iff hd).mp hf, ht,
      fun j hj he => hprev j hj ((flag_iff hd).mpr (of_decide_eq_true he))⟩

/-- Output one means that a first circle flag below the endpoint lies below one half. -/
theorem dyadicFirstFlagSign_eq_one_iff {d B r : ℕ} (hd : 0 < d) (N : ℕ → ℕ) :
    dyadicFirstFlagSign d B r N = 1 ↔
      ∃ k < r, FirstCircleFlag (1 / (d : ℚ)) (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k ∧
        (N k : ℚ) / (2 : ℚ) ^ B < 1 / 2 := by
  rw [dyadicFirstFlagSign, firstEventSign_eq_one_iff, first_test_iff hd]
  simp only [decide_eq_true_eq, ← left_iff]

/-- Output minus one means that the first circle flag lies above one half.
Uniqueness of the first flag rules out the competing positive test. -/
theorem dyadicFirstFlagSign_eq_neg_one_iff {d B r : ℕ} (hd : 0 < d) (N : ℕ → ℕ) :
    dyadicFirstFlagSign d B r N = -1 ↔
      ∃ k < r, FirstCircleFlag (1 / (d : ℚ)) (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k ∧
        1 / 2 < (N k : ℚ) / (2 : ℚ) ^ B := by
  rw [dyadicFirstFlagSign, firstEventSign_eq_neg_one_iff]
  rw [first_test_iff hd N (fun k => decide (2 * N k < 2 ^ B)),
    first_test_iff hd N (fun k => decide (2 ^ B < 2 * N k))]
  simp only [decide_eq_true_eq, ← left_iff, ← right_iff]
  constructor
  · exact And.right
  · intro hright
    refine ⟨?_, hright⟩
    rintro ⟨j, _, hj, hleft⟩
    obtain ⟨k, _, hk, hright⟩ := hright
    obtain rfl := hj.unique hk
    linarith

/-- Output zero means that neither strict side occurs at a first flag.
In particular, a first value exactly one half gives zero. -/
theorem dyadicFirstFlagSign_eq_zero_iff {d B r : ℕ} (hd : 0 < d) (N : ℕ → ℕ) :
    dyadicFirstFlagSign d B r N = 0 ↔
      (¬ ∃ k < r, FirstCircleFlag (1 / (d : ℚ)) (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k ∧
        (N k : ℚ) / (2 : ℚ) ^ B < 1 / 2) ∧
      ¬ ∃ k < r, FirstCircleFlag (1 / (d : ℚ)) (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k ∧
        1 / 2 < (N k : ℚ) / (2 : ℚ) ^ B := by
  rw [dyadicFirstFlagSign, firstEventSign_eq_zero_iff]
  rw [first_test_iff hd N (fun k => decide (2 * N k < 2 ^ B)),
    first_test_iff hd N (fun k => decide (2 ^ B < 2 * N k))]
  simp only [decide_eq_true_eq, ← left_iff, ← right_iff]

private theorem firstEventSign_freeze {α : Type} (event positive negative : α × ℕ → Bool)
    (r : α → ℕ) (x : α) :
    firstEventSign (fun p : Unit × ℕ => event (x, p.2))
      (fun p => positive (x, p.2)) (fun p => negative (x, p.2)) (fun _ => r x) () =
      firstEventSign event positive negative r x := by
  have htest (test : α × ℕ → Bool) :
      firstEventTest (fun p : Unit × ℕ => event (x, p.2)) (fun p => test (x, p.2))
        (fun _ => r x) () = firstEventTest event test r x := by
    rw [Bool.eq_iff_iff, firstEventTest_eq_true_iff, firstEventTest_eq_true_iff]
  simp only [firstEventSign, htest]

namespace CountingFunction

/-- Classifying the first dyadic flag costs two function levels beyond its numerator evaluator.
The binary margin denominator, unary precision, binary endpoint, scale and all arithmetic tests
are charged. This is a classifier certificate and assumes no integer sign-correctness property. -/
theorem dyadicFirstFlagSign_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {N : α × ℕ → ℕ} {d B r : α → ℕ}
    (hN : N ∈ CountingFunction a (encPair enc encNat) encNat)
    (hd : ComputableInPolyTime d enc encNat) (hB : ComputableInPolyTime B enc encUnary)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x => dyadicFirstFlagSign (d x) (B x) (r x) (fun k => N (x, k))) ∈
      CountingFunction (a + 2) enc encIntBin := by
  have hd' : ComputableInPolyTime (fun p : α × ℕ => d p.1)
      (encPair enc encNat) encNat := hd.comp (ComputableInPolyTime.fst _ _)
  have hs : ComputableInPolyTime (fun p : α × ℕ => 2 ^ B p.1)
      (encPair enc encNat) encNat :=
    (ComputableInPolyTime.binary_two_pow.comp hB).comp (ComputableInPolyTime.fst _ _)
  have hu : ComputableInPolyTime (fun p : α × ℕ => (d p.1 - 1) * 2 ^ B p.1)
      (encPair enc encNat) encNat := by fun_prop
  have hmul := nat_mul (of_polyTime hd') hN
  have hlo := map (prod (of_polyTime hs) hmul) ComputableInPolyTime.binary_le
  have hhi := map (prod hmul (of_polyTime hu)) ComputableInPolyTime.binary_le
  have hevent := map (output := encBool) (prod hlo hhi)
    (ComputableInPolyTime.of_finite (fun p : Bool × Bool => p.1 && p.2))
  have htwice := nat_mul (of_polyTime (ComputableInPolyTime.const 2)) hN
  have hleft := nat_lt htwice (of_polyTime hs)
  have hright := nat_lt (of_polyTime hs) htwice
  have h := firstEventSign_mem_CountingFunction D hevent hleft hright hr
  convert h using 1
  funext x
  simp only [dyadicFirstFlagSign, Bool.decide_and]
  exact firstEventSign_freeze
    (fun p : α × ℕ => decide (2 ^ B p.1 ≤ d p.1 * N p) &&
      decide (d p.1 * N p ≤ (d p.1 - 1) * 2 ^ B p.1))
    (fun p => decide (2 * N p < 2 ^ B p.1))
    (fun p => decide (2 ^ B p.1 < 2 * N p)) r x

end CountingFunction
end Cslib.Complexity
