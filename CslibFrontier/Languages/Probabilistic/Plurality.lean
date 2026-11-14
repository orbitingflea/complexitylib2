/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Repeat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.List.MinMax
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Plurality amplification for probabilistic computations

For a list `xs : List α` over a type with decidable equality, `Cslib.ProbComp.plurality default xs`
returns the element of `xs` occurring most frequently (breaking ties in favor of the first element
in `xs` achieving the maximum frequency, and returning `default` on `[]`). Whenever an element `a`
appears strictly more than `xs.length / 2` times, `plurality default xs = a`
(`Cslib.ProbComp.plurality_eq_of_length_lt_two_mul_count`), because any two distinct elements appear
at most `xs.length` times in total (`Cslib.ProbComp.count_add_count_le_length_of_ne`).

By Hoeffding's inequality (`Cslib.Probability.PMF.pi_sum_le_mean_sub`), if a probabilistic
computation `program : ProbComp α` outputs `a` with probability at least `1 / 2 + γ` (`0 ≤ γ`), then
the plurality of `k` independent runs differs from `a` with probability at most `exp (-2 * k * γ²)`
(`Cslib.ProbComp.toOuterMeasure_plurality_replicate_ne_toReal_le`), and therefore outputs `a` with
probability at least `1 - exp (-2 * k * γ²) ≥ 1 - 2^{-(2 * γ² * k)}`
(`Cslib.ProbComp.one_sub_exp_le_eval_plurality_replicate_toReal`,
`Cslib.ProbComp.one_sub_two_rpow_le_eval_plurality_replicate_toReal`).

## Main definitions

* `Cslib.ProbComp.plurality`: most frequent element of a list, with tie-breaking by first
  occurrence and a default value on `[]`.

## Main results

* `Cslib.ProbComp.count_add_count_le_length_of_ne`: two distinct elements appear at most `xs.length`
  times in total.
* `Cslib.ProbComp.plurality_eq_of_length_lt_two_mul_count`: strict majority implies plurality.
* `Cslib.ProbComp.toOuterMeasure_plurality_replicate_ne_toReal_le`,
  `Cslib.ProbComp.one_sub_exp_le_eval_plurality_replicate_toReal`,
  `Cslib.ProbComp.one_sub_two_rpow_le_eval_plurality_replicate_toReal`: Hoeffding concentration for
  the plurality of `k` independent runs of a `ProbComp α` with margin `γ` above `1 / 2`.
-/

public section

namespace Cslib.ProbComp

open Cslib.Probability

/-- The most frequent element of `xs`, breaking ties in favor of the earliest element of `xs`
achieving the maximum frequency, or `default` when `xs` is empty. -/
@[expose]
def plurality {α : Type*} [DecidableEq α] (default : α) (xs : List α) : α :=
  (xs.argmax (fun x => xs.count x)).getD default

/-- Two distinct elements appear at most `xs.length` times in total. -/
theorem count_add_count_le_length_of_ne {α : Type*} [DecidableEq α] (xs : List α) {a b : α}
    (hab : a ≠ b) : xs.count a + xs.count b ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.count_cons, List.count_cons, List.length_cons]
    by_cases hxa : x = a
    · subst hxa
      have hxb : (x == b) = false := beq_eq_false_iff_ne.mpr hab
      simp only [beq_self_eq_true, ↓reduceIte, hxb, Bool.false_eq_true]
      omega
    · have hxa' : (x == a) = false := beq_eq_false_iff_ne.mpr hxa
      have hxb' : (if x == b then 1 else 0) ≤ 1 := by split_ifs <;> omega
      simp only [hxa', Bool.false_eq_true, ↓reduceIte]
      omega

/-- Whenever `a` appears strictly more than half the time in `xs`, `plurality default xs = a`. -/
theorem plurality_eq_of_length_lt_two_mul_count {α : Type*} [DecidableEq α] (default : α)
    {xs : List α} {a : α} (h : xs.length < 2 * xs.count a) :
    plurality default xs = a := by
  have hpos : 0 < xs.count a := by omega
  have ha : a ∈ xs := List.count_pos_iff.mp hpos
  have hne : xs ≠ [] := List.ne_nil_of_mem ha
  unfold plurality
  rcases hm : xs.argmax (fun x => xs.count x) with _ | m
  · exact (hne (List.argmax_eq_none.mp hm)).elim
  · simp only [Option.getD_some]
    have hle : xs.count a ≤ xs.count m := List.le_of_mem_argmax ha hm
    by_contra hma
    have hsum := count_add_count_le_length_of_ne xs (Ne.symm hma)
    omega

private theorem count_true_map_beq {α : Type*} [DecidableEq α] (xs : List α) (a : α) :
    (xs.map (· == a)).count true = xs.count a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [List.count_cons, ih]

private theorem eval_map_beq_true {α : Type} [DecidableEq α] (program : ProbComp α) (a : α) :
    ProbComp.eval ((· == a) <$> program) true = ProbComp.eval program a := by
  rw [ProbComp.eval_map, PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    simp [beq_iff_eq, hba]

private theorem countTrue_le_mean_sub (count : ℕ) (program : ProbComp Bool) {ε : ℝ} (hε : 0 ≤ ε) :
    ((ProbComp.eval (OracleComp.countTrue count program)).toOuterMeasure {successes |
      (successes : ℝ) ≤ count * (ProbComp.eval program true).toReal - ε}).toReal ≤
        Real.exp (-2 * ε ^ 2 / count) := by
  rw [ProbComp.eval_countTrue, PMF.toOuterMeasure_map_apply]
  have h := Cslib.Probability.PMF.pi_sum_le_mean_sub (fun _ : Fin count => ProbComp.eval program)
    (fun _ bit => (bit.toNat : ℝ)) (bound := 1) (by norm_num)
    (by intro i bit _; cases bit <;> norm_num) hε
  simpa [Set.preimage_ofPred_eq, Nat.cast_sum, Fintype.sum_bool] using h

private theorem exp_neg_le_two_rpow_neg {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ (2 : ℝ) ^ (-x) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), Real.exp_le_exp]
  have hlog : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    linarith [Real.add_one_le_exp 1]
  nlinarith

/-- **Plurality concentration for `k` independent trials.** If a closed probabilistic program
`program : ProbComp α` outputs `a` with probability at least `1 / 2 + γ` (for `0 ≤ γ`), then the
plurality of `k` independent runs differs from `a` with probability at most
`exp (-2 * k * γ²)`. -/
theorem toOuterMeasure_plurality_replicate_ne_toReal_le {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    ((ProbComp.eval (plurality default <$> OracleComp.replicate k program)).toOuterMeasure
        {y | y ≠ a}).toReal ≤ Real.exp (-2 * k * γ ^ 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, mul_zero, zero_mul, Real.exp_zero]
    exact Cslib.Probability.PMF.toOuterMeasure_toReal_le_one _ _
  have hcount := countTrue_le_mean_sub k ((· == a) <$> program) (ε := k * γ) (by positivity)
  rw [eval_map_beq_true] at hcount
  have hexp : -2 * ((k : ℝ) * γ) ^ 2 / k = -2 * k * γ ^ 2 := by
    have hk0 : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
    field_simp
  rw [hexp] at hcount
  refine le_trans ?_ hcount
  simp only [OracleComp.countTrue, OracleComp.replicate_map, Functor.map_map, ProbComp.eval_map,
    PMF.toOuterMeasure_map_apply]
  have hsub : (ProbComp.eval (OracleComp.replicate k program)).toOuterMeasure
      (plurality default ⁻¹' {y | y ≠ a}) ≤
      (ProbComp.eval (OracleComp.replicate k program)).toOuterMeasure
        ((fun xs : List α => (xs.map (· == a)).count true) ⁻¹'
          {successes | (successes : ℝ) ≤ k * (ProbComp.eval program a).toReal - k * γ}) := by
    rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply]
    refine tsum_le_tsum fun xs => ?_
    by_cases hsupp : xs ∈ (ProbComp.eval (OracleComp.replicate k program)).support
    · have hlen : xs.length = k := ((ProbComp.mem_support_replicate_iff k program xs).mp hsupp).1
      by_cases hxs : xs ∈ plurality default ⁻¹' {y | y ≠ a}
      · have hmem' : xs ∈ (fun xs : List α => (xs.map (· == a)).count true) ⁻¹'
            {successes : ℕ | (successes : ℝ) ≤ k * (ProbComp.eval program a).toReal - k * γ} := by
          simp only [Set.mem_preimage, Set.mem_ofPred_eq, count_true_map_beq] at hxs ⊢
          have hle_len : 2 * xs.count a ≤ k := by
            rw [← hlen]
            by_contra hlt
            exact hxs (plurality_eq_of_length_lt_two_mul_count default (not_le.mp hlt))
          have hle_real : (2 : ℝ) * xs.count a ≤ k := by exact_mod_cast hle_len
          nlinarith
        rw [Set.indicator_of_mem hxs, Set.indicator_of_mem hmem']
      · rw [Set.indicator_of_notMem hxs]
        exact zero_le
    · have h0 : ProbComp.eval (OracleComp.replicate k program) xs = 0 :=
        (PMF.apply_eq_zero_iff _ _).mpr hsupp
      simp [Set.indicator_apply, h0]
  exact ENNReal.toReal_mono (Cslib.Probability.PMF.toOuterMeasure_ne_top _ _) hsub

/-- **Plurality success probability for `k` independent trials.** If `program` outputs `a` with
probability at least `1 / 2 + γ` (`0 ≤ γ`), then the plurality of `k` independent runs outputs `a`
with probability at least `1 - exp (-2 * k * γ²) ≥ 1 - 2^{-(2 * γ² * k)}`. -/
theorem one_sub_exp_le_eval_plurality_replicate_toReal {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    1 - Real.exp (-2 * k * γ ^ 2) ≤
      (ProbComp.eval (plurality default <$> OracleComp.replicate k program) a).toReal := by
  set p := ProbComp.eval (plurality default <$> OracleComp.replicate k program)
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl p ({a} : Set α)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({a} : Set α)ᶜ = {y | y ≠ a} := rfl
  rw [hcompl_set] at hcompl
  linarith [toOuterMeasure_plurality_replicate_ne_toReal_le default a k program hγ hp]

/-- Base-`2` exponential form of `one_sub_exp_le_eval_plurality_replicate_toReal`. -/
theorem one_sub_two_rpow_le_eval_plurality_replicate_toReal {α : Type} [DecidableEq α]
    (default a : α) (k : ℕ) (program : ProbComp α) {γ : ℝ} (hγ : 0 ≤ γ)
    (hp : 1 / 2 + γ ≤ (ProbComp.eval program a).toReal) :
    1 - (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) ≤
      (ProbComp.eval (plurality default <$> OracleComp.replicate k program) a).toReal := by
  have hexp : Real.exp (-2 * k * γ ^ 2) ≤ (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) := by
    rw [show -2 * (k : ℝ) * γ ^ 2 = -(2 * γ ^ 2 * k) by ring]
    exact exp_neg_le_two_rpow_neg (by positivity)
  linarith [one_sub_exp_le_eval_plurality_replicate_toReal default a k program hγ hp]

end Cslib.ProbComp
