/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Probability.Collision
import CslibFrontier.Probability.IID.Birthday
import CslibFrontier.Probability.IID.Distinct
import Mathlib.Data.Nat.Choose.Cast

/-!
# Collisions of a function on uniform samples

For a function `f : M → β` whose values lie in a finite set `D`, and `s` independent uniform
samples `x : Fin s → M`, this module bounds from below the probability that two samples are
different points with the same value under `f`:

`1 - exp (-s (s - 1) / (2 |D|)) - C(s, 2) / |M| ≤ P(∃ i j, f (x i) = f (x j) ∧ x i ≠ x j)`.

This is the probabilistic content of [BonehShoup2023], §8.3, Lemma 8.2 (printed p. 294), with its
two error terms kept explicit. The first term is Theorem B.1(i) for the pushforward law of the
values, which is not uniform in general; the proof applies
`Cslib.Probability.PMF.one_sub_exp_neg_le_iid_not_injective`, which holds for every law. The second
term bounds the probability that two samples are the same point, by the union bound
`Cslib.Probability.PMF.iid_not_injective_le`.

## Differences from [BonehShoup2023]

* Lemma 8.2 is stated for a hash function `H : M → T` with `N = |T|`. Here `f` is any function
  with values in a finite set `D`, and `|D|` plays the part of `N`.
* The book bounds the probability that two samples are equal messages by Theorem B.1(ii), which
  gives at most `1/5` for its parameters. Here the union bound `C(s, 2) / |M|` is used. It needs no
  side condition, and for the book's parameters it is at most `0.06`.
* The book's constants are `3/4 - 1/5 > 1/2`. Here they are `1 - 1/4 - 1/8 ≥ 1/2`.

## Main results

* `Cslib.Probability.PMF.one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision`: the
  lower bound displayed above.
* `Cslib.Probability.PMF.half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le`: with the book's
  parameters `|M| ≥ 100 N` and `s = ⌈2 √N⌉ + 1`, the bound is at least `1/2`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §8.3, Lemma 8.2 and Algorithm BirthdayAttack (printed
  pp. 294–295); Appendix B.1, Theorem B.1 (printed p. 1101).
-/

public section

namespace Cslib.Probability.PMF

variable {M β : Type} [Fintype M] [Nonempty M]

/-- **Collisions of a function on uniform samples** (the probabilistic content of
[BonehShoup2023], §8.3, Lemma 8.2, printed p. 294, with explicit error terms): if every value of
`f` lies in the finite set `D`, then among `s` independent uniform samples two are different points
with the same value of `f` with probability at least
`1 - exp (-s (s - 1) / (2 |D|)) - C(s, 2) / |M|`. -/
theorem one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision (f : M → β)
    (D : Finset β) (hf : ∀ m, f m ∈ D) (s : ℕ) :
    1 - Real.exp (-(s * (s - 1) / (2 * D.card))) - s.choose 2 * (Fintype.card M : ℝ)⁻¹ ≤
      ((iid (uniformOfFintype M) s).toOuterMeasure
        {x | ∃ i j, f (x i) = f (x j) ∧ x i ≠ x j}).toReal := by
  classical
  set μ := iid (uniformOfFintype M) s
  let g : M → D := fun m => ⟨f m, hf m⟩
  have hvalues : 1 - Real.exp (-(s * (s - 1) / (2 * D.card))) ≤
      (μ.toOuterMeasure {x | ¬ Function.Injective fun i => g (x i)}).toReal := by
    have h := one_sub_exp_neg_le_iid_not_injective ((uniformOfFintype M).map g) s
    rwa [iid_map, PMF.toOuterMeasure_map_apply, Fintype.card_coe] at h
  have hpoints : (μ.toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤
      s.choose 2 * (Fintype.card M : ℝ)⁻¹ := by
    have h := iid_not_injective_le (uniformOfFintype M) s
    rwa [collisionProbability_uniform] at h
  have hsub : {x : Fin s → M | ¬ Function.Injective fun i => g (x i)} ⊆
      {x | ∃ i j, f (x i) = f (x j) ∧ x i ≠ x j} ∪ {x | ¬ Function.Injective x} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Function.Injective, not_forall] at hx
    obtain ⟨i, j, hij, hne⟩ := hx
    by_cases hm : x i = x j
    · exact Or.inr fun hinj => hne (hinj hm)
    · exact Or.inl ⟨i, j, congrArg Subtype.val hij, hm⟩
  have hunion : (μ.toOuterMeasure {x | ¬ Function.Injective fun i => g (x i)}).toReal ≤
      (μ.toOuterMeasure {x | ∃ i j, f (x i) = f (x j) ∧ x i ≠ x j}).toReal +
        (μ.toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
    rw [← ENNReal.toReal_add (toOuterMeasure_ne_top _ _) (toOuterMeasure_ne_top _ _)]
    exact ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨toOuterMeasure_ne_top _ _, toOuterMeasure_ne_top _ _⟩)
      ((MeasureTheory.measure_mono hsub).trans (MeasureTheory.measure_union_le _ _))
  linarith

/-- The bound of `one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision` is at least
`1/2` once `s (s - 1) ≥ 4 N` and `K ≥ 4 s (s - 1)`: then `exp (-s (s - 1) / (2 N)) ≤ 1/4` and
`C(s, 2) / K ≤ 1/8`. -/
private theorem half_le_one_sub_exp_neg_sub_choose {N K s : ℕ} (hN : 0 < N)
    (hs : 4 * (N : ℝ) ≤ s * (s - 1)) (hK : 4 * ((s : ℝ) * (s - 1)) ≤ K) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-(s * (s - 1) / (2 * N))) - s.choose 2 * (K : ℝ)⁻¹ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hK' : (0 : ℝ) < K := by nlinarith
  have hexp : Real.exp (-(s * (s - 1) / (2 * N))) ≤ 1 / 4 := by
    refine (Real.exp_le_half_pow 2 ?_).trans_eq (by norm_num)
    rw [neg_le_neg_iff, le_div_iff₀ (by positivity)]
    push_cast
    linarith
  have hch : (s.choose 2 : ℝ) * (K : ℝ)⁻¹ ≤ 1 / 8 := by
    rw [Nat.cast_choose_two, ← div_eq_mul_inv, div_le_iff₀ hK']
    linarith
  linarith

/-- **The parameters of Lemma 8.2** ([BonehShoup2023], §8.3, Algorithm BirthdayAttack, printed
p. 294): for `K ≥ 100 N` and `s = ⌈2 √N⌉ + 1`,
`1/2 ≤ 1 - exp (-s (s - 1) / (2 N)) - C(s, 2) / K`. With `r = ⌈2 √N⌉`, `4 N ≤ r (r + 1) ≤ 12 N`. -/
theorem half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le {N K : ℕ} (hN : 0 < N)
    (hK : 100 * N ≤ K) :
    (1 / 2 : ℝ) ≤ 1 - Real.exp (-(((⌈2 * Real.sqrt N⌉₊ + 1 : ℕ) : ℝ) *
        (((⌈2 * Real.sqrt N⌉₊ + 1 : ℕ) : ℝ) - 1) / (2 * N))) -
      (⌈2 * Real.sqrt N⌉₊ + 1).choose 2 * (K : ℝ)⁻¹ := by
  set r := ⌈2 * Real.sqrt N⌉₊
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt N ^ 2 = N := Real.sq_sqrt (by positivity)
  have hsq0 : 0 ≤ Real.sqrt N := Real.sqrt_nonneg _
  have hsq1 : Real.sqrt N ≤ N := by nlinarith
  have hr1 : 2 * Real.sqrt N ≤ r := Nat.le_ceil _
  have hr2 : (r : ℝ) < 2 * Real.sqrt N + 1 := Nat.ceil_lt_add_one (by positivity)
  have hK' : (100 : ℝ) * N ≤ K := by exact_mod_cast hK
  refine half_le_one_sub_exp_neg_sub_choose hN ?_ ?_
  · push_cast; nlinarith
  · push_cast; nlinarith

end Cslib.Probability.PMF
