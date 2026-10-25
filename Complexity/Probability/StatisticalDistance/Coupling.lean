/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/StatisticalDistance.lean`)

public import Cslib.Probability.StatisticalDistance
public import Complexity.Probability.PMF
import Complexity.Probability.PMF.Event

/-!
# The coupling inequality

Two functions of one sample are at statistical distance at most the probability that they differ
(`Cslib.Probability.PMF.dist_map_map_le`). The sample space may be infinite; only the common
codomain is finite.

## Main results

* `Cslib.Probability.PMF.dist_map_map_le`: the coupling inequality.
-/

@[expose] public section

open scoped Cslib.Probability.PMF

namespace Cslib.Probability.PMF

variable {α β : Type*}

private theorem dist_map_map_le_of_finite [Finite α] [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  classical
  have := Fintype.ofFinite α
  rw [dist_eq, toOuterMeasure_apply_toReal]
  have hmap : ∀ (h : α → β) (b : β),
      ((p.map h) b).toReal = ∑ a, if h a = b then (p a).toReal else 0 := by
    intro h b
    rw [PMF.map_apply, tsum_fintype,
      ENNReal.toReal_sum fun a _ => by split_ifs <;> simp [PMF.apply_ne_top]]
    exact Finset.sum_congr rfl fun a _ => by by_cases hab : b = h a <;> simp [hab, eq_comm]
  have hpt : ∀ b, |((p.map f) b).toReal - ((p.map g) b).toReal| ≤
      ∑ a, (p a).toReal * |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)| := by
    intro b
    rw [hmap, hmap, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => ?_))
    have hp := ENNReal.toReal_nonneg (a := p a)
    split_ifs <;> simp [abs_of_nonneg hp]
  have hinner : ∀ a, ∑ b, |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)| =
      if f a ≠ g a then 2 else 0 := by
    intro a
    by_cases hfg : f a = g a
    · simp [hfg]
    · rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (f a)),
        Finset.sum_eq_single_of_mem (g a) (by simp [Ne.symm hfg])]
      · simp only [↓reduceIte, Ne.symm hfg, sub_zero, abs_one, hfg, zero_sub, abs_neg, ne_eq,
          not_false_eq_true]
        norm_num
      · intro b hb hbg
        have hbf : b ≠ f a := by simpa using hb
        simp [Ne.symm hbf, Ne.symm hbg]
  calc (∑ b, |((p.map f) b).toReal - ((p.map g) b).toReal|) / 2
      ≤ (∑ b, ∑ a, (p a).toReal *
          |(if f a = b then (1 : ℝ) else 0) - (if g a = b then 1 else 0)|) / 2 := by
        gcongr with b
        exact hpt b
    _ = _ := by
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, hinner]
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun a _ => ?_
        by_cases hfg : f a = g a <;> simp [hfg]

/-- **Coupling inequality.** Two functions of the same sample are at statistical distance at most
the probability that they differ. -/
theorem dist_map_map_le [Fintype β] (p : PMF α) (f g : α → β) :
    dist (p.map f) (p.map g) ≤ (p.toOuterMeasure {a | f a ≠ g a}).toReal := by
  have h := dist_map_map_le_of_finite (p.map fun a => (f a, g a)) Prod.fst Prod.snd
  rwa [PMF.map_comp, PMF.map_comp, PMF.toOuterMeasure_map_apply] at h

end Cslib.Probability.PMF
