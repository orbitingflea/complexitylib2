/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
import CslibFrontier.Probability.Concentration
import CslibFrontier.Probability.PoissonBinomial
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Hoeffding's inequality for the biased binomial distribution

For a Bernoulli trial with parameter `p ∈ [0, 1]`, the centered moment generating function
`(1 - p) exp (-s p) + p exp (s (1 - p))` is bounded above by `exp (s² / 8)` for every `s : ℝ`
(`Cslib.one_sub_mul_exp_add_mul_exp_le`), by Mathlib’s bounded-variable sub-Gaussian estimate.
The binomial theorem gives the centered MGF identity (`Cslib.sum_choose_mul_pow_mul_exp`).
Specializing finite-PMF concentration to independent coins and using the replicated
Poisson-binomial law gives one-sided (`Cslib.sum_filter_le_sub_choose_mul_pow_le`,
`Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`) and two-sided
(`Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`) Hoeffding tail bounds for `Bin(Q, p)`, together
with the interval-complement form (`Cslib.sum_filter_notMem_choose_mul_pow_le`) used in Lemma 4.8 of
`[OpenAI2026ETH]` at `p = (r - 1) / (2 r)`. All tail inequalities hold for every `Q : ℕ`, including
`Q = 0`.

For the unbiased case `p = 1 / 2` in counting form on `ι → Bool`, see
`Cslib.BitString.card_filter_le_abs_card_filter_sub_half_le`.

## Main results

* `Cslib.one_sub_mul_exp_add_mul_exp_le`: Hoeffding's lemma for a biased Bernoulli trial.
* `Cslib.sum_choose_mul_pow_eq_one`: binomial probability weights sum to `1`.
* `Cslib.choose_mul_pow_le_mode`: the binomial weight is largest at the mode `n p` when that is an
  integer.
* `Cslib.sum_choose_mul_pow_mul_exp`: centered moment generating function of `Bin(Q, p)`.
* `Cslib.sum_filter_le_sub_choose_mul_pow_le`: upper-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_mul_sub_choose_mul_pow_le`: lower-tail Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_le_abs_sub_choose_mul_pow_le`: two-sided Hoeffding bound for `Bin(Q, p)`.
* `Cslib.sum_filter_notMem_choose_mul_pow_le`: tail bound outside a subset covering
  `[Q p - t, Q p + t]`.

## References

* [W. Hoeffding, *Probability Inequalities for Sums of Bounded Random Variables*][Hoeffding1963]
* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Section 4.7, Lemma 4.8,
  pp. 34–35.
-/

public section

namespace Cslib

open Finset Real
open MeasureTheory

/-- **Hoeffding's lemma for a biased Bernoulli trial** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`s : ℝ`, the centered moment generating function `(1 - p) exp (-s p) + p exp (s (1 - p))` is at
most `exp (s² / 8)`. This specializes Mathlib's bounded-variable sub-Gaussian estimate. -/
theorem one_sub_mul_exp_add_mul_exp_le {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) (s : ℝ) :
    (1 - p) * exp (-s * p) + p * exp (s * (1 - p)) ≤ exp (s ^ 2 / 8) := by
  let q : unitInterval := ⟨p, hp₀, hp₁⟩
  let μ := ProbabilityTheory.bernoulliMeasure true false q
  let X : Bool → ℝ := fun b => if b then 1 else 0
  have hmean : ∫ b, X b ∂μ = p := by
    rw [ProbabilityTheory.integral_bernoulliMeasure]
    simp [X, q]
  have h := ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc (μ := μ)
    (X := X) (a := 0) (b := 1) (by fun_prop)
    (MeasureTheory.ae_of_all _ fun b => by cases b <;> norm_num [X])
  have hmgf := h.mgf_le s
  rw [ProbabilityTheory.mgf, ProbabilityTheory.integral_bernoulliMeasure] at hmgf
  simp only [hmean, X, ↓reduceIte, smul_eq_mul, sub_zero, nnnorm_one,
    NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at hmgf
  change p * exp (s * (1 - p)) + (1 - p) * exp (s * (0 - p)) ≤
    exp (((1 : ℝ) / 2) ^ 2 * s ^ 2 / 2) at hmgf
  have hexp : s * (0 - p) = -s * p := by ring
  rw [hexp] at hmgf
  convert hmgf using 1
  · ring
  · congr 1
    ring

/-- The binomial weights `C(Q, k) p^k (1 - p)^(Q - k)` sum to `1`. -/
theorem sum_choose_mul_pow_eq_one (Q : ℕ) (p : ℝ) :
    ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) = 1 := by
  calc ∑ k ∈ range (Q + 1), (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
      = ∑ k ∈ range (Q + 1), p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) :=
          sum_congr rfl fun _ _ => by ring
    _ = (p + (1 - p)) ^ Q := (add_pow p (1 - p) Q).symm
    _ = 1 := by simp only [add_sub_cancel, one_pow]

/-- **The centered binomial moment generating function**: summing
`C(Q, k) p^k (1 - p)^(Q - k) exp (s (k - Q p))` over `0 ≤ k ≤ Q` factors as the `Q`-th power of
the single-trial moment generating function. -/
theorem sum_choose_mul_pow_mul_exp (Q : ℕ) (p s : ℝ) :
    ∑ k ∈ range (Q + 1),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p)) =
    ((1 - p) * exp (-s * p) + p * exp (s * (1 - p))) ^ Q := by
  rw [add_comm ((1 - p) * exp (-s * p)), add_pow]
  refine sum_congr rfl fun k hk => ?_
  have hkQ : k ≤ Q := Nat.lt_succ_iff.mp (mem_range.mp hk)
  rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
  calc (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) * exp (s * ((k : ℝ) - Q * p))
      = p ^ k * (1 - p) ^ (Q - k) * (Q.choose k : ℝ) *
          (exp (↑k * (s * (1 - p))) * exp (↑(Q - k) * (-s * p))) := by
        rw [← exp_add, Nat.cast_sub hkQ]
        have hexp : s * ((k : ℝ) - Q * p) =
            (k : ℝ) * (s * (1 - p)) + ((Q : ℝ) - k) * (-s * p) := by ring
        rw [hexp]
        ring
    _ = p ^ k * exp (↑k * (s * (1 - p))) *
          ((1 - p) ^ (Q - k) * exp (↑(Q - k) * (-s * p))) * (Q.choose k : ℝ) := by ring

/-- Every binomial probability weight `C(Q, k) p^k (1 - p)^(Q - k)` is nonnegative for
`p ∈ [0, 1]`. -/
private theorem choose_mul_pow_nonneg (Q k : ℕ) {p : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1) :
    0 ≤ (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp₁
  positivity

/-- Express an event of the replicated Poisson-binomial law as a finite binomial sum. -/
private theorem poissonBinomial_event_toReal (Q : ℕ) (p : unitInterval) (P : ℕ → Prop)
    [DecidablePred P] :
    ((Probability.PMF.poissonBinomial (List.replicate Q p)).toOuterMeasure {k | P k}).toReal =
      ∑ k ∈ range (Q + 1) with P k,
        (Q.choose k : ℝ) * (p : ℝ) ^ k * (1 - p) ^ (Q - k) := by
  rw [_root_.PMF.toOuterMeasure_apply]
  have hfinite : (∑' k, ({k | P k} : Set ℕ).indicator
      (Probability.PMF.poissonBinomial (List.replicate Q p)) k) =
      ∑ k ∈ range (Q + 1), if P k then
        Probability.PMF.poissonBinomial (List.replicate Q p) k else 0 := by
    rw [tsum_eq_sum (s := range (Q + 1))]
    · exact sum_congr rfl fun k _ => by simp [Set.indicator_apply]
    · intro k hk
      have hkQ : Q < k := by
        simpa only [mem_range, not_lt, Nat.succ_le_iff] using hk
      have hz := Probability.PMF.poissonBinomial_eq_zero_of_lt
        (ps := List.replicate Q p) (by simpa using hkQ)
      simp [Set.indicator_apply, hz]
  rw [hfinite, ENNReal.toReal_sum]
  · simp only [sum_filter]
    exact sum_congr rfl fun k _ => by
      split_ifs <;> simp [Probability.PMF.poissonBinomial_replicate_apply_toReal]
  · intro k _
    split_ifs <;> simp [_root_.PMF.apply_ne_top]

/-- **Upper-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `k - Q p ≥ t` is at most `exp (-2 t² / Q)`. At `Q = 0` the right-hand
side is `exp 0 = 1`. -/
theorem sum_filter_le_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ ((k : ℕ) : ℝ) - Q * p,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  classical
  let q : unitInterval := ⟨p, hp₀, hp₁⟩
  let ps := List.replicate Q q
  let trials := Probability.PMF.pi fun i : Fin ps.length => Probability.PMF.coin ps[i]
  let count : (Fin ps.length → Bool) → ℕ := fun f => ∑ i, if f i then 1 else 0
  have hmean : (∑ i : Fin ps.length, ∑ b : Bool,
      (Probability.PMF.coin ps[i] b).toReal * (if b then (1 : ℝ) else 0)) = Q * p := by
    simp [ps, q, Probability.PMF.coin_apply_toReal]
  have hcount (f : Fin ps.length → Bool) :
      (count f : ℝ) = ∑ i, if f i then (1 : ℝ) else 0 := by
    simp [count]
  have h := Probability.PMF.pi_sum_ge_mean_add
    (fun i : Fin ps.length => Probability.PMF.coin ps[i])
    (fun _ b => if b then (1 : ℝ) else 0) (bound := 1) (by norm_num)
    (fun _ b _ => by cases b <;> norm_num) ht
  rw [hmean] at h
  simp only [Fintype.card_fin, ps, List.length_replicate, one_pow, mul_one] at h
  have hevent : {f : Fin ps.length → Bool | Q * p + t ≤ ∑ i, if f i then (1 : ℝ) else 0} =
      count ⁻¹' {k | t ≤ (k : ℝ) - Q * p} := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, hcount]
    constructor <;> intro h <;> linarith
  rw [hevent, ← _root_.PMF.toOuterMeasure_map_apply] at h
  have hlaw : trials.map count = Probability.PMF.poissonBinomial ps :=
    (Probability.PMF.poissonBinomial_eq_map_pi ps).symm
  change ((trials.map count).toOuterMeasure _).toReal ≤ _ at h
  rw [hlaw, poissonBinomial_event_toReal Q q] at h
  exact h

/-- **Lower-tail Hoeffding inequality for `Bin(Q, p)`**: for `p ∈ [0, 1]` and `0 ≤ t`, the
binomial probability mass on `Q p - k ≥ t` is at most `exp (-2 t² / Q)`. The reflection
`k ↦ Q - k` turns it into the upper tail of `Bin(Q, 1 - p)`. -/
theorem sum_filter_le_mul_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ Q * p - ((k : ℕ) : ℝ),
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    exp (-2 * t ^ 2 / Q) := by
  refine le_of_eq_of_le ?_
    (sum_filter_le_sub_choose_mul_pow_le Q (sub_nonneg.2 hp₁) (sub_le_self 1 hp₀) ht)
  rw [sum_filter, sum_filter, ← sum_range_reflect]
  refine sum_congr rfl fun j hj => ?_
  have hjQ : j ≤ Q := Nat.lt_succ_iff.1 (mem_range.1 hj)
  rw [add_tsub_cancel_right, Nat.cast_sub hjQ, Nat.choose_symm hjQ, Nat.sub_sub_self hjQ,
    sub_sub_cancel, show (Q : ℝ) * p - (Q - j) = j - Q * (1 - p) by ring, mul_right_comm]

/-- **Two-sided Hoeffding inequality for `Bin(Q, p)`** `[Hoeffding1963]`: for `p ∈ [0, 1]` and
`0 ≤ t`, the binomial probability mass on `|k - Q p| ≥ t` is at most `2 exp (-2 t² / Q)`. -/
theorem sum_filter_le_abs_sub_choose_mul_pow_le (Q : ℕ) {p t : ℝ} (hp₀ : 0 ≤ p) (hp₁ : p ≤ 1)
    (ht : 0 ≤ t) :
    ∑ k ∈ range (Q + 1) with t ≤ |((k : ℕ) : ℝ) - Q * p|,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  let w : ℕ → ℝ := fun k => (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k)
  let A : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ (k : ℝ) - Q * p
  let B : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ Q * p - (k : ℝ)
  let C : Finset ℕ := (range (Q + 1)).filter fun k : ℕ => t ≤ |(k : ℝ) - Q * p|
  have hsub : C ⊆ A ∪ B := by
    intro k hk
    simp only [C, A, B, mem_filter, mem_union] at hk ⊢
    rcases le_abs.mp hk.2 with h | h
    · exact Or.inl ⟨hk.1, h⟩
    · exact Or.inr ⟨hk.1, by linarith⟩
  have hunion : ∑ k ∈ A ∪ B, w k ≤ ∑ k ∈ A, w k + ∑ k ∈ B, w k := by
    have h := sum_union_inter (s₁ := A) (s₂ := B) (f := w)
    have hinter : 0 ≤ ∑ k ∈ A ∩ B, w k :=
      sum_nonneg fun k _ => choose_mul_pow_nonneg Q k hp₀ hp₁
    linarith
  calc ∑ k ∈ C, w k
      ≤ ∑ k ∈ A ∪ B, w k :=
        sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => choose_mul_pow_nonneg Q k hp₀ hp₁
    _ ≤ ∑ k ∈ A, w k + ∑ k ∈ B, w k := hunion
    _ ≤ exp (-2 * t ^ 2 / Q) + exp (-2 * t ^ 2 / Q) :=
        add_le_add (sum_filter_le_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
          (sum_filter_le_mul_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
    _ = 2 * exp (-2 * t ^ 2 / Q) := by ring

/-- **Interval-complement Hoeffding bound for `Bin(Q, p)`**: if `I` contains every integer
`0 ≤ k ≤ Q` within `t` of the mean `Q p`, then the binomial mass outside `I` is at most
`2 exp (-2 t² / Q)`. -/
theorem sum_filter_notMem_choose_mul_pow_le (Q : ℕ) (I : Finset ℕ) {p t : ℝ} (hp₀ : 0 ≤ p)
    (hp₁ : p ≤ 1) (ht : 0 ≤ t)
    (hI : ∀ k ∈ range (Q + 1), |(k : ℝ) - Q * p| ≤ t → k ∈ I) :
    ∑ k ∈ range (Q + 1) with k ∉ I,
      (Q.choose k : ℝ) * p ^ k * (1 - p) ^ (Q - k) ≤
    2 * exp (-2 * t ^ 2 / Q) := by
  refine (sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ =>
    choose_mul_pow_nonneg Q k hp₀ hp₁).trans (sum_filter_le_abs_sub_choose_mul_pow_le Q hp₀ hp₁ ht)
  intro k hk
  simp only [mem_filter] at hk ⊢
  refine ⟨hk.1, ?_⟩
  rcases le_or_gt (|(k : ℝ) - Q * p|) t with hle | hgt
  · exact False.elim (hk.2 (hI k hk.1 hle))
  · exact hgt.le

/-- **The mode of the binomial distribution**: when `n p = w` is an integer, the weight
`C(n, k) p ^ k (1 - p) ^ (n - k)` of `Bin(n, p)` is largest at `k = w`. Consecutive weights satisfy
`t (k + 1) (k + 1) (1 - p) = t k (n - k) p`, so they increase up to `w` and decrease after it. -/
theorem choose_mul_pow_le_mode {n w : ℕ} {p : ℝ} (hw : w ≤ n) (hnp : (n : ℝ) * p = w)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {k : ℕ} (hk : k ≤ n) :
    (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) ≤ n.choose w * p ^ w * (1 - p) ^ (n - w) := by
  set t : ℕ → ℝ := fun k => (n.choose k : ℝ) * p ^ k * (1 - p) ^ (n - k) with ht
  have ht0 : ∀ k, 0 ≤ t k := fun k => by simp only [t]; have := sub_nonneg.mpr hp1; positivity
  -- `t (k + 1) (k + 1) (1 - p) = t k (n - k) p`
  have hstep : ∀ k < n, t (k + 1) * ((k + 1) * (1 - p)) = t k * ((n - k : ℝ) * p) := by
    intro k hk
    have hc : (n.choose (k + 1) : ℝ) * (k + 1) = n.choose k * (n - k : ℝ) := by
      rw [← Nat.cast_sub hk.le]; exact_mod_cast Nat.choose_succ_right_eq n k
    have he : (1 - p) ^ (n - k) = (1 - p) ^ (n - (k + 1)) * (1 - p) := by
      rw [← pow_succ]; congr 1; omega
    simp only [t]
    rw [he, pow_succ]
    linear_combination (p ^ k * p * (1 - p) ^ (n - (k + 1)) * (1 - p)) * hc
  have hup : ∀ k, k < w → t k ≤ t (k + 1) := by
    intro k hkw
    have hkn : (k : ℝ) + 1 ≤ w := by exact_mod_cast hkw
    have hwn : (w : ℝ) ≤ n := by exact_mod_cast hw
    have hp : 0 < p := by
      rcases hp0.eq_or_lt with h | h
      · rw [← h, mul_zero] at hnp; linarith
      · exact h
    have hpos : (0 : ℝ) < (n - k) * p := mul_pos (by linarith) hp
    have hcmp : ((k : ℝ) + 1) * (1 - p) ≤ (n - k) * p := by nlinarith
    have := hstep k (by exact_mod_cast (show (k : ℝ) < n by linarith))
    have h2 := mul_le_mul_of_nonneg_left hcmp (ht0 (k + 1))
    exact le_of_mul_le_mul_right (by linarith) hpos
  have hdown : ∀ k, w ≤ k → k < n → t (k + 1) ≤ t k := by
    intro k hwk hkn
    have hwk' : (w : ℝ) ≤ k := by exact_mod_cast hwk
    have hkn' : (k : ℝ) < n := by exact_mod_cast hkn
    have hp1' : 0 < 1 - p := by nlinarith
    have hpos : (0 : ℝ) < (k + 1) * (1 - p) := mul_pos (by positivity) hp1'
    have hcmp : ((n : ℝ) - k) * p ≤ (k + 1) * (1 - p) := by nlinarith
    have := hstep k hkn
    have h2 := mul_le_mul_of_nonneg_left hcmp (ht0 k)
    exact le_of_mul_le_mul_right (by linarith) hpos
  change t k ≤ t w
  rcases le_total k w with hkw | hwk
  · have key : ∀ j, k + j ≤ w → t k ≤ t (k + j) := by
      intro j
      induction j with
      | zero => intro _; exact le_rfl
      | succ j ih => intro h; exact (ih (by omega)).trans (hup _ (by omega))
    simpa [Nat.add_sub_cancel' hkw] using key (w - k) (by omega)
  · have key : ∀ j, w + j ≤ n → t (w + j) ≤ t w := by
      intro j
      induction j with
      | zero => intro _; exact le_rfl
      | succ j ih => intro h; exact (hdown (w + j) (by omega) (by omega)).trans (ih (by omega))
    simpa [Nat.add_sub_cancel' hwk] using key (k - w) (by omega)

end Cslib
