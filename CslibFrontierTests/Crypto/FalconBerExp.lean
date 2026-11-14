/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Computational.Falcon.BerExp

/-!
# Tests for the Falcon v1.2 BerExp threshold distribution

These ordinary-import clients check the strict deterministic boundary and exact acceptance masses
at thresholds zero, one, one half of the 64-bit range, and the maximal unsigned value.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.FalconBerExp

open Cslib Cslib.Crypto.Falcon

public section

private abbrev zeroThreshold : BerExpThreshold := ⟨0, by norm_num⟩
private abbrev oneThreshold : BerExpThreshold := ⟨1, by norm_num⟩
private abbrev halfThreshold : BerExpThreshold := ⟨2 ^ 63, by norm_num⟩
private abbrev maxThreshold : BerExpThreshold := ⟨2 ^ 64 - 1, by norm_num⟩

/-- The strict comparison accepts zero below threshold one, but rejects equality and every sample
at threshold zero. -/
example : berExpThresholdAccepts oneThreshold zeroThreshold.val = true ∧
    berExpThresholdAccepts oneThreshold oneThreshold.val = false ∧
    berExpThresholdAccepts zeroThreshold zeroThreshold.val = false := by decide

/-- Threshold zero has zero acceptance mass. -/
example : (ProbComp.eval (berExpThresholdCoin zeroThreshold) true).toReal = 0 := by
  rw [eval_berExpThresholdCoin_true_toReal]
  norm_num

/-- Threshold one accepts exactly one of the `2^64` uniform words. -/
example : (ProbComp.eval (berExpThresholdCoin oneThreshold) true).toReal =
    1 / (2 ^ 64 : ℝ) := by
  rw [eval_berExpThresholdCoin_true_toReal]
  norm_num

/-- The midpoint threshold is an exact fair coin. -/
example : (ProbComp.eval (berExpThresholdCoin halfThreshold) true).toReal = 1 / 2 := by
  rw [eval_berExpThresholdCoin_true_toReal]
  norm_num

/-- The maximal 64-bit threshold rejects exactly the single equal word. -/
example : (ProbComp.eval (berExpThresholdCoin maxThreshold) false).toReal =
    1 / (2 ^ 64 : ℝ) := by
  rw [eval_berExpThresholdCoin_false_toReal]
  norm_num

end

end CslibFrontierTests.Crypto.FalconBerExp
