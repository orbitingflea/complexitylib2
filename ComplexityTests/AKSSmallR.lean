/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.NumberTheory.AKS.SmallR

/-! A small modulus of large order: instances. -/

namespace ComplexityTests.AKSSmallR

open Cslib.AKS

-- For `n = 1000`, some `r ≤ 4 · 10⁵` has order above `⌈log₂ 1000⌉² = 100`.
example : ∃ r, 2 ≤ r ∧ r ≤ 4 * Nat.clog 2 1000 ^ 5 ∧
    Nat.clog 2 1000 ^ 2 < orderOf ((1000 : ℕ) : ZMod r) := exists_lt_orderOf (by norm_num)

example : ∃ r : ℕ, 2 ≤ r ∧ (r : ℝ) ≤ 128 * Real.logb 2 (7 : ℕ) ^ 5 ∧
    Real.logb 2 (7 : ℕ) ^ 2 < orderOf ((7 : ℕ) : ZMod r) := exists_lt_orderOf_logb (by norm_num)

-- `C(6, 3) = 20` divides `lcm(1, …, 6) = 60`.
example : Nat.centralBinom 3 ∣ 60 :=
  centralBinom_dvd_of_forall_dvd (by norm_num) fun s hs hs6 => by interval_cases s <;> decide

end ComplexityTests.AKSSmallR
