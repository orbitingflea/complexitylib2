/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.ParallelRepetition.Recursion

/-! # The recursion of the parallel repetition theorem

The sequence `p_m = v^m` (independent play of an optimal strategy) satisfies the hypotheses of
Holenstein's recursion, so the conclusion applies to it.
-/

namespace ComplexityTests.RepetitionRecursion

open Cslib.PCP.ParallelRepetition

example {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    v ^ n ≤ ((1 + v) / 2) ^ ⌊(1 - v) ^ 2 * n / (13 * 15 ^ 2 * 1)⌋₊ :=
  le_pow_floor_of_step (C := 15) (L := 1) (p := fun m => v ^ m) hv hv1 (by norm_num) le_rfl
    (pow_zero v) (fun m => pow_nonneg hv m) (fun m => by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hv m) hv1)
    fun m _ => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (pow_nonneg hv m)

-- The exponential form, for the same sequence.
example {v : ℝ} (hv : 0 ≤ v) (hv1 : v ≤ 1) (n : ℕ) :
    v ^ n ≤ 2 * (1 - (1 - v) ^ 3 / (26 * 15 ^ 2)) ^ ((n : ℝ) / 1) :=
  le_two_mul_rpow_of_step (C := 15) (L := 1) (p := fun m => v ^ m) hv hv1 (by norm_num) le_rfl
    (pow_zero v) (fun m => pow_nonneg hv m) (fun m => by
      simpa [pow_succ] using mul_le_of_le_one_right (pow_nonneg hv m) hv1)
    fun m _ => by
      rw [pow_succ]
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (by positivity))
        (pow_nonneg hv m)

end ComplexityTests.RepetitionRecursion
