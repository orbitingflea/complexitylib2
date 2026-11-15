/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.IID
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Foundations.Analysis.BernoulliInequality
import CslibFrontier.Foundations.Analysis.SpecialFunctions.DescFactorialExp
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Lower bounds on the birthday collision probability

For `k` independent samples of a law `μ` on a finite type `α` with `n = Fintype.card α` elements,
this module bounds from below the probability that two samples are equal, the event
`{x | ¬ Function.Injective x}` under `iid μ k`, for every law, and computes it for the uniform law:

* for every law the samples are distinct with probability at most `(n)_k / n ^ k`
  (`iid_injective_le_descFactorial_div_pow`), and for the uniform law exactly `(n)_k / n ^ k`
  (`iid_uniformOfFintype_injective`), so the uniform law minimizes the collision probability;
* for every law the collision probability is at least
  `1 - exp (-k (k - 1) / (2 n)) ≥ min (k (k - 1) / (4 n), 0.63)`
  ([BonehShoup2023], Theorem B.1(i) and Corollary B.2);
* for the uniform law it is at most `1 - exp (-k (k - 1) / n)` when `2 k ≤ n + 2`
  ([BonehShoup2023], Theorem B.1(ii)).

The upper bounds for every law, from the union bound, are in
`CslibFrontier.Probability.IID.Distinct` (`Cslib.Probability.PMF.iid_not_injective_le`). For the
uniform law that bound is `k (k - 1) / (2 n)`, which is below Theorem B.1(ii)'s bound whenever
`k (k - 1) / n ≤ 1.59`.

The first item is the work. The mass of the injective `k`-tuples with entries in a finite set,
for nonnegative point weights with a given sum, is largest for equal weights; this is a weak form
of Maclaurin's inequality. The proof adds one point of the set at a time, and the step is
the tangent-line form of Bernoulli's inequality, `Real.pow_add_mul_sub_le_pow`.

## Differences from [BonehShoup2023]

* Corollary B.2 assumes `k ≥ 2`. That hypothesis is dropped: both lower bounds are `0` for `k ≤ 1`.
* Theorem B.1(ii) assumes `k < n / 2`. It is proved here under `2 k ≤ n + 2`, which `k < n / 2`
  implies.
* The proof of Corollary B.2 (that the uniform law minimizes the collision probability) is this
  library's own, by the induction above. It is not the book's argument, which moves mass between
  two points of unequal mass.

## Main results

* `Cslib.Probability.PMF.iid_injective_le_descFactorial_div_pow`: for every law, `k` samples are
  distinct with probability at most `(n)_k / n ^ k`.
* `Cslib.Probability.PMF.iid_uniformOfFintype_injective`: `k` uniform samples are distinct with
  probability `(n)_k / n ^ k`.
* `Cslib.Probability.PMF.one_sub_exp_neg_le_iid_not_injective`,
  `Cslib.Probability.PMF.min_le_iid_not_injective`: the two lower bounds of Theorem B.1(i) and
  Corollary B.2, for every law.
* `Cslib.Probability.PMF.iid_uniformOfFintype_not_injective_le_one_sub_exp_neg`: the upper bound of
  Theorem B.1(ii).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Appendix B.1, Theorem B.1 and Corollary B.2 (printed p. 1101).
-/

public section

namespace Cslib.Probability.PMF

/-- `min (x / 2) 0.63 ≤ 1 - exp (-x)` for `0 ≤ x`. The constant `0.63` is below
`1 - exp (-1) = 0.632…`. -/
private theorem min_div_two_le_one_sub_exp_neg {x : ℝ} (h0 : 0 ≤ x) :
    min (x / 2) 0.63 ≤ 1 - Real.exp (-x) := by
  rcases le_total x 1 with h1 | h1
  · exact (min_le_left _ _).trans (by linarith [Real.exp_neg_le_one_sub_div_two h0 h1])
  · refine (min_le_right _ _).trans ?_
    have h2 : Real.exp (-x) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
    have h3 := Real.exp_neg_one_lt_d9
    norm_num at h3 ⊢
    linarith

/-! ### Mass of injective tuples -/

section DistinctMass

variable {α : Type*} [DecidableEq α]

/-- Total weight of the injective `k`-tuples with entries in `s`, for point weights `p`. -/
private def distinctMass (p : α → ℝ) : ℕ → Finset α → ℝ
  | 0, _ => 1
  | k + 1, s => ∑ a ∈ s, p a * distinctMass p k (s.erase a)

@[simp] private theorem distinctMass_zero (p : α → ℝ) (s : Finset α) :
    distinctMass p 0 s = 1 := rfl

private theorem distinctMass_succ (p : α → ℝ) (k : ℕ) (s : Finset α) :
    distinctMass p (k + 1) s = ∑ a ∈ s, p a * distinctMass p k (s.erase a) := rfl

/-- Adding a point `x` to `s` adds the tuples that use `x` in one of their `k + 1` places. -/
private theorem distinctMass_insert (p : α → ℝ) : ∀ (k : ℕ) (s : Finset α) (x : α), x ∉ s →
    distinctMass p (k + 1) (insert x s) =
      distinctMass p (k + 1) s + (k + 1) * (p x * distinctMass p k s)
  | 0, s, x, hx => by
    simp only [distinctMass_succ, distinctMass_zero, mul_one, Finset.sum_insert hx, Nat.cast_zero,
      zero_add, one_mul]
    exact add_comm _ _
  | k + 1, s, x, hx => by
    have key : ∀ a ∈ s, p a * distinctMass p (k + 1) ((insert x s).erase a) =
        p a * distinctMass p (k + 1) (s.erase a) +
          (k + 1) * (p x * (p a * distinctMass p k (s.erase a))) := by
      intro a ha
      have hax : x ≠ a := fun h => hx (h ▸ ha)
      rw [Finset.erase_insert_of_ne hax,
        distinctMass_insert p k (s.erase a) x (fun h => hx (Finset.mem_of_mem_erase h))]
      ring
    rw [distinctMass_succ p (k + 1) (insert x s), Finset.sum_insert hx, Finset.erase_insert hx,
      Finset.sum_congr rfl key, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← distinctMass_succ, ← distinctMass_succ]
    push_cast; ring

private theorem cast_sub_mul_descFactorial (m k : ℕ) :
    ((m - k : ℕ) : ℝ) * (m.descFactorial k : ℝ) = ((m : ℝ) - k) * m.descFactorial k := by
  rcases le_or_gt k m with h | h
  · rw [Nat.cast_sub h]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 h]; simp

/-- The inductive step of `distinctMass_le`: the bounds for a set of `m` points with total weight
`S` give the bound after adding a point of weight `px`. -/
private theorem distinctMass_le_step (k m : ℕ) {S px A B : ℝ} (hS : 0 ≤ S) (hpx : 0 ≤ px)
    (hS0 : m = 0 → S = 0) (hA : A ≤ (m.descFactorial (k + 1) : ℝ) * (S / m) ^ (k + 1))
    (hB : B ≤ (m.descFactorial k : ℝ) * (S / m) ^ k) :
    A + (k + 1) * (px * B) ≤
      ((m + 1).descFactorial (k + 1) : ℝ) * ((px + S) / ((m + 1 : ℕ) : ℝ)) ^ (k + 1) := by
  have ht0 : 0 ≤ S / m := div_nonneg hS (Nat.cast_nonneg m)
  have hmt : (m : ℝ) * (S / m) = S := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · simp [h0, hS0 h0]
    · have : (m : ℝ) ≠ 0 := by exact_mod_cast h0.ne'
      field_simp
  have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
  have hu0 : 0 ≤ (px + S) / ((m + 1 : ℕ) : ℝ) := div_nonneg (add_nonneg hpx hS) hm1.le
  have hmu : ((m + 1 : ℕ) : ℝ) * ((px + S) / ((m + 1 : ℕ) : ℝ)) = px + S := by
    have := hm1.ne'
    field_simp
  have hpxu : px = ((m + 1 : ℕ) : ℝ) * ((px + S) / ((m + 1 : ℕ) : ℝ)) - m * (S / m) := by
    rw [hmt, hmu]; ring
  generalize S / (m : ℝ) = t at *
  generalize (px + S) / ((m + 1 : ℕ) : ℝ) = u at *
  rw [Nat.descFactorial_succ, Nat.cast_mul, cast_sub_mul_descFactorial] at hA
  rw [Nat.succ_descFactorial_succ, Nat.cast_mul]
  have h1 : (k + 1 : ℝ) * (px * B) ≤ (k + 1) * (px * (m.descFactorial k * t ^ k)) := by gcongr
  calc A + (k + 1) * (px * B)
      ≤ ((m : ℝ) - k) * m.descFactorial k * t ^ (k + 1) +
          (k + 1) * (px * (m.descFactorial k * t ^ k)) := add_le_add hA h1
    _ = ((m + 1 : ℕ) : ℝ) * m.descFactorial k * (t ^ (k + 1) + (k + 1) * t ^ k * (u - t)) := by
        rw [hpxu]; push_cast; ring
    _ ≤ ((m + 1 : ℕ) : ℝ) * m.descFactorial k * u ^ (k + 1) := by
        gcongr; exact Real.pow_add_mul_sub_le_pow hu0 ht0 k

/-- Among nonnegative weights on `s` with a given sum, equal weights maximize the mass of injective
`k`-tuples: a weak form of Maclaurin's inequality. -/
private theorem distinctMass_le (p : α → ℝ) (s : Finset α) (hp : ∀ a ∈ s, 0 ≤ p a) (k : ℕ) :
    distinctMass p k s ≤ (s.card.descFactorial k : ℝ) * ((∑ a ∈ s, p a) / s.card) ^ k := by
  induction s using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp
    | succ k => simp [distinctMass_succ]
  | insert x s hx ih =>
    have hps : ∀ a ∈ s, 0 ≤ p a := fun a ha => hp a (Finset.mem_insert_of_mem ha)
    cases k with
    | zero => simp
    | succ k =>
      rw [distinctMass_insert p k s x hx, Finset.card_insert_of_notMem hx, Finset.sum_insert hx]
      exact distinctMass_le_step k s.card (Finset.sum_nonneg hps)
        (hp x (Finset.mem_insert_self x s))
        (fun h => by rw [Finset.card_eq_zero.1 h, Finset.sum_empty]) (ih hps (k + 1)) (ih hps k)

/-- For constant weights `c`, the mass of injective `k`-tuples in `s` is `(|s|)_k c ^ k`. -/
private theorem distinctMass_const (c : ℝ) : ∀ (k : ℕ) (s : Finset α),
    distinctMass (fun _ => c) k s = (s.card.descFactorial k : ℝ) * c ^ k
  | 0, s => by simp
  | k + 1, s => by
    have key : ∀ a ∈ s, c * distinctMass (fun _ => c) k (s.erase a) =
        c * (((s.card - 1).descFactorial k : ℝ) * c ^ k) := fun a ha => by
      rw [distinctMass_const c k (s.erase a), Finset.card_erase_of_mem ha]
    rw [distinctMass_succ, Finset.sum_congr rfl key, Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos s.card with h | h
    · simp [h]
    · obtain ⟨m, hm⟩ : ∃ m, s.card = m + 1 := ⟨s.card - 1, by omega⟩
      rw [hm, Nat.succ_descFactorial_succ, Nat.add_sub_cancel]; push_cast; ring

/-- `distinctMass p k s` is the sum of `∏ i, p (v i)` over the injective `v : Fin k → α` with values
in `s`. -/
private theorem sum_injective_eq_distinctMass [Fintype α] (p : α → ℝ) :
    ∀ (k : ℕ) (s : Finset α),
      (∑ v : Fin k → α, if Function.Injective v ∧ ∀ i, v i ∈ s then ∏ i, p (v i) else 0) =
        distinctMass p k s
  | 0, s => by simp [Function.injective_of_subsingleton]
  | k + 1, s => by
    have key : ∀ a : α,
        (∑ w : Fin k → α, if Function.Injective (Fin.cons a w : Fin (k + 1) → α) ∧
            ∀ i, (Fin.cons a w : Fin (k + 1) → α) i ∈ s
          then ∏ i, p ((Fin.cons a w : Fin (k + 1) → α) i) else 0) =
          if a ∈ s then p a * distinctMass p k (s.erase a) else 0 := by
      intro a
      rw [← sum_injective_eq_distinctMass p k (s.erase a)]
      split_ifs with ha
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun w _ => ?_
        have hiff : (Function.Injective (Fin.cons a w : Fin (k + 1) → α) ∧
            ∀ i, (Fin.cons a w : Fin (k + 1) → α) i ∈ s) ↔
            (Function.Injective w ∧ ∀ i, w i ∈ s.erase a) := by
          rw [Fin.cons_injective_iff, Fin.forall_fin_succ]
          simp only [Fin.cons_zero, Fin.cons_succ, Finset.mem_erase, Set.mem_range, not_exists]
          constructor
          · rintro ⟨⟨h1, h2⟩, -, h4⟩; exact ⟨h2, fun i => ⟨h1 i, h4 i⟩⟩
          · rintro ⟨h2, h3⟩; exact ⟨⟨fun i => (h3 i).1, h2⟩, ha, fun i => (h3 i).2⟩
        by_cases h : Function.Injective w ∧ ∀ i, w i ∈ s.erase a
        · rw [ite_eq_left (hiff.2 h), ite_eq_left h, Fin.prod_univ_succ]; simp
        · rw [ite_eq_right (mt hiff.1 h), ite_eq_right h, mul_zero]
      · refine Finset.sum_eq_zero fun w _ => ite_eq_right ?_
        rintro ⟨-, h⟩
        exact ha (by simpa using h 0)
    rw [distinctMass_succ, ← (Fin.consEquiv fun _ : Fin (k + 1) => α).sum_comp,
      Fintype.sum_prod_type]
    refine (Finset.sum_congr rfl fun a _ => key a).trans ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]

end DistinctMass

/-! ### Distinct samples and collisions -/

variable {α : Type*}

private theorem iid_injective_toReal [Fintype α] [DecidableEq α] (μ : PMF α) (k : ℕ) :
    ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal =
      distinctMass (fun a => (μ a).toReal) k Finset.univ := by
  rw [toOuterMeasure_apply_toReal, ← sum_injective_eq_distinctMass]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [iid_apply, ENNReal.toReal_prod]

/-- For every law `μ` on a finite type with `n` elements, `k` independent samples are distinct with
probability at most `(n)_k / n ^ k`, which is the probability for the uniform law
(`iid_uniformOfFintype_injective`): the uniform law maximizes the probability that the samples are
distinct. -/
theorem iid_injective_le_descFactorial_div_pow [Fintype α] (μ : PMF α) (k : ℕ) :
    ((iid μ k).toOuterMeasure {x | Function.Injective x}).toReal ≤
      (Fintype.card α).descFactorial k / (Fintype.card α : ℝ) ^ k := by
  classical
  rw [iid_injective_toReal]
  have h := distinctMass_le (fun a => (μ a).toReal) Finset.univ
    (fun a _ => ENNReal.toReal_nonneg) k
  rw [sum_toReal, Finset.card_univ, one_div, inv_pow] at h
  rwa [div_eq_mul_inv]

/-- `k` independent uniform samples from a finite type with `n` elements are distinct with
probability `(n)_k / n ^ k`. -/
theorem iid_uniformOfFintype_injective [Fintype α] [Nonempty α] (k : ℕ) :
    ((iid (PMF.uniformOfFintype α) k).toOuterMeasure {x | Function.Injective x}).toReal =
      (Fintype.card α).descFactorial k / (Fintype.card α : ℝ) ^ k := by
  classical
  rw [iid_injective_toReal]
  have : (fun a => ((PMF.uniformOfFintype α) a).toReal) = fun _ => ((Fintype.card α : ℝ))⁻¹ := by
    funext a; simp [PMF.uniformOfFintype_apply]
  rw [this, distinctMass_const, Finset.card_univ, inv_pow, div_eq_mul_inv]

/-- [BonehShoup2023], Theorem B.1(i) and Corollary B.2, first inequality: `k` independent samples
of any law `μ` on a finite type with `n` elements contain two equal samples with probability at
least `1 - exp (-k (k - 1) / (2 n))`. Theorem B.1(i) is the case of the uniform law. Corollary B.2
assumes `k ≥ 2`; that is not needed, since the bound is `0` for `k ≤ 1`. -/
theorem one_sub_exp_neg_le_iid_not_injective [Fintype α] (μ : PMF α) (k : ℕ) :
    1 - Real.exp (-(k * (k - 1) / (2 * Fintype.card α))) ≤
      ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
  have hc := toOuterMeasure_toReal_add_compl (iid μ k) {x | Function.Injective x}
  change _ + ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal = 1 at hc
  have := (iid_injective_le_descFactorial_div_pow μ k).trans
    (Nat.descFactorial_div_pow_le_exp _ k)
  linarith

/-- [BonehShoup2023], Theorem B.1(i) and Corollary B.2, second inequality: `k` independent samples
of any law on a finite type with `n` elements contain two equal samples with probability at least
`min (k (k - 1) / (4 n)) 0.63`. As in `one_sub_exp_neg_le_iid_not_injective`, Corollary B.2's
`k ≥ 2` is not needed. -/
theorem min_le_iid_not_injective [Fintype α] (μ : PMF α) (k : ℕ) :
    min ((k : ℝ) * (k - 1) / (4 * Fintype.card α)) 0.63 ≤
      ((iid μ k).toOuterMeasure {x | ¬ Function.Injective x}).toReal := by
  refine le_trans ?_ (one_sub_exp_neg_le_iid_not_injective μ k)
  have h0 : (0 : ℝ) ≤ k * (k - 1) / (2 * Fintype.card α) := by
    rcases Nat.eq_zero_or_pos k with h | h
    · simp [h]
    · have h1 : (1 : ℝ) ≤ k := by exact_mod_cast h
      exact div_nonneg (mul_nonneg (Nat.cast_nonneg k) (by linarith)) (by positivity)
  have e : (k : ℝ) * (k - 1) / (4 * Fintype.card α) = k * (k - 1) / (2 * Fintype.card α) / 2 := by
    ring
  rw [e]
  exact min_div_two_le_one_sub_exp_neg h0

/-- [BonehShoup2023], Theorem B.1(ii): `k` independent uniform samples from a finite type with `n`
elements contain two equal samples with probability at most `1 - exp (-k (k - 1) / n)` when
`2 k ≤ n + 2`. The book assumes `k < n / 2`, which implies `2 k ≤ n + 2`. -/
theorem iid_uniformOfFintype_not_injective_le_one_sub_exp_neg [Fintype α] [Nonempty α] {k : ℕ}
    (hk : 2 * k ≤ Fintype.card α + 2) :
    ((iid (PMF.uniformOfFintype α) k).toOuterMeasure {x | ¬ Function.Injective x}).toReal ≤
      1 - Real.exp (-(k * (k - 1) / Fintype.card α)) := by
  have hc := toOuterMeasure_toReal_add_compl (iid (PMF.uniformOfFintype α) k)
    {x | Function.Injective x}
  change _ + ((iid (PMF.uniformOfFintype α) k).toOuterMeasure
    {x | ¬ Function.Injective x}).toReal = 1 at hc
  rw [iid_uniformOfFintype_injective] at hc
  linarith [Nat.exp_le_descFactorial_div_pow (n := Fintype.card α) Fintype.card_pos hk]

end Cslib.Probability.PMF
