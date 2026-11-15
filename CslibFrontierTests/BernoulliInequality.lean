/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Analysis.BernoulliInequality

/-!
# Tests for the forms of Bernoulli's inequality

Checks for `CslibFrontier/Foundations/Analysis/BernoulliInequality.lean` as a `module` client with
an ordinary import: the tangent-line form at `y = 1` is Bernoulli's inequality on `[0, ∞)`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BernoulliInequality

/-- At `y = 1` the tangent-line inequality is Bernoulli's inequality
`1 + (n + 1) (x - 1) ≤ x ^ (n + 1)` for `0 ≤ x`. -/
example {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 1 + (n + 1) * (x - 1) ≤ x ^ (n + 1) := by
  simpa using Real.pow_add_mul_sub_le_pow hx zero_le_one n

end CslibFrontierTests.BernoulliInequality
