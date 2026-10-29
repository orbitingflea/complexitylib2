/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Probability.PMF

/-!
# Infinite-Series Expectations over `PMF.map` and `PMF.bind`

Countable-sum (`tsum`) expectation identities for `ℝ≥0∞`-valued functions under `PMF.map` and
`PMF.bind` on arbitrary (not necessarily finite) discrete sample spaces; see
[MitzenmacherUpfal2017], Sections 2.1 and 2.3.

## Main results

* `Cslib.Probability.PMF.tsum_map_mul`: expectation of `k : β → ℝ≥0∞` under `p.map g` equals the
  expectation of `k ∘ g` under `p`.
* `Cslib.Probability.PMF.tsum_bind_mul`: expectation of `k : β → ℝ≥0∞` under `p.bind f` decomposes
  as an iterated expectation.

## References

* [M. Mitzenmacher and E. Upfal, *Probability and Computing*][MitzenmacherUpfal2017],
  Sections 2.1 and 2.3.
-/

@[expose] public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α β : Type*}

/-- Expectation of `k : β → ℝ≥0∞` under `p.map g` equals expectation of `k ∘ g` under `p`. -/
theorem tsum_map_mul (p : PMF α) (g : α → β) (k : β → ℝ≥0∞) :
    (∑' b, p.map g b * k b) = ∑' a, p a * k (g a) := by
  simp only [PMF.map_apply, ← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm]
  refine tsum_congr fun a => ?_
  rw [tsum_eq_single (g a)]
  · simp
  · intro b hb
    simp [hb]

/-- Expectation of `k : β → ℝ≥0∞` under `p.bind f` decomposes as an iterated expectation. -/
theorem tsum_bind_mul (p : PMF α) (f : α → PMF β) (k : β → ℝ≥0∞) :
    (∑' b, (p.bind f) b * k b) = ∑' a, p a * ∑' b, f a b * k b := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left, mul_assoc]
  exact ENNReal.tsum_comm

end Cslib.Probability.PMF

end
