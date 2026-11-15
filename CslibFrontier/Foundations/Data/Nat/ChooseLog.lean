/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.Choose
import CslibFrontier.Foundations.Data.Nat.Log

/-!
# Ceiling-logarithm comparison between tuples and subsets

Encoding `n` elements from a universe of size `U` separately in base `b > 1` uses `n * ⌈log_b U⌉`
digits, whereas encoding an `n`-subset of a `U`-element set uses `⌈log_b C(U, n)⌉` digits. Because
`b ^ ⌈log_b U⌉ ≤ b * U` (`Nat.pow_clog_le_mul`) and `U ^ n ≤ n ^ n * C(U, n)`
(`Nat.choose_mul_pow_le`), any power bound `n ≤ b ^ E` yields
`n * ⌈log_b U⌉ ≤ n + n * E + ⌈log_b C(U, n)⌉` (`Nat.mul_clog_le_add_clog_choose`).

## Main results

* `Nat.mul_clog_le_add_clog_choose`: `n * ⌈log_b U⌉ ≤ n + n * E + ⌈log_b C(U, n)⌉` whenever
  `1 < b`, `n ≤ U`, and `n ≤ b ^ E`.
-/

public section

namespace Nat

/-- Encoding `n` elements of a `U`-element universe separately in base `b > 1` exceeds the subset
cost `⌈log_b C(U, n)⌉` by at most `n + n * E` digits whenever `n ≤ U` and `n ≤ b ^ E`. -/
theorem mul_clog_le_add_clog_choose {b U n E : ℕ} (hb : 1 < b) (hnU : n ≤ U) (hpow : n ≤ b ^ E) :
    n * clog b U ≤ n + n * E + clog b (U.choose n) := by
  rcases eq_zero_or_pos n with rfl | hn
  · simp
  · have hpow_U : b ^ clog b U ≤ b * U := pow_clog_le_mul hb (hn.trans_le hnU).ne'
    have hchoose : U ^ n ≤ n ^ n * U.choose n := by
      simpa [choose_self, Nat.mul_comm] using choose_mul_pow_le hnU n
    have hclog_choose : U.choose n ≤ b ^ clog b (U.choose n) := le_pow_clog hb (U.choose n)
    refine (Nat.pow_le_pow_iff_right hb).mp ?_
    calc b ^ (n * clog b U)
        = (b ^ clog b U) ^ n := by rw [Nat.mul_comm, Nat.pow_mul]
      _ ≤ (b * U) ^ n := Nat.pow_le_pow_left hpow_U n
      _ = b ^ n * U ^ n := Nat.mul_pow b U n
      _ ≤ b ^ n * (n ^ n * U.choose n) := Nat.mul_le_mul_left _ hchoose
      _ ≤ b ^ n * ((b ^ E) ^ n * b ^ clog b (U.choose n)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.pow_le_pow_left hpow n) hclog_choose)
      _ = b ^ (n + n * E + clog b (U.choose n)) := by
          rw [← Nat.pow_mul, Nat.mul_comm E n, ← Nat.pow_add, ← Nat.pow_add, ← Nat.add_assoc]

end Nat

end
