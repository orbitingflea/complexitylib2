/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.SelfReduction
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# The DL and CDH self-reductions in a fixed group: checked instances

Clients of `CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction.lean` under module
encapsulation, with ordinary imports.

* In `ZMod 5` with `g = 1`, an adversary that is right only on the challenge `0` has advantage
  `1 / 5`. It never finds the logarithm of `3`, yet one masked call and one attempt of
  `dlSelfReduce` on `3` return `3` with probability `1 / 5`. Five attempts fail with probability
  `(4 / 5) ^ 5 ≤ exp (-1)` and succeed with probability `1 - (4 / 5) ^ 5 ≥ 1 - exp (-1)`, and `k`
  attempts fail with probability at most `exp (-(k / 5))`.
* An adversary that is never right makes every attempt fail, so `0 < ε` is needed in the iteration
  bound.
* In `ZMod 4` with `g = 2`, which has order `2`, the constant guess `0` has advantage `1 / 4`. One
  attempt on `0` returns each of the two logarithms `0` and `2` of `0` with probability `1 / 4`, so
  it does not fail with probability `1 - 1 / 4`: the exact failure probability needs injectivity
  of `c ↦ c • g`, while the upper bound `(1 - 1 / 4) ^ k` does not. An input outside the image of
  `c ↦ c • g` makes every attempt fail.
* In `ZMod 5`, the two-sided CDH self-reduction succeeds with probability `1 / 5` on every input
  for an adversary that is right only when its second input is `0`, while masking the first input
  alone succeeds with probability `1` or `0` depending on the second input.
* The book's algorithm `B`, transcribed with its test `g^α₁ = u · g^σ`, has the same law as
  `dlSelfReduce q g A 1`.
-/

public section

namespace CslibFrontierTests.Crypto.DiffieHellmanSelfReduction

open Cslib Cslib.Probability Cslib.Crypto
open scoped NNReal ENNReal

/-! ### The book's algorithm `B` -/

section General

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)
  [DecidableEq G]

/-- The algorithm `B` in the proof of [BonehShoup2023], Theorem 10.2 (p. 412), transcribed:
`σ ← Zq, u₁ ← u · g^σ, α₁ ← A(u₁)`, then `fail` unless `g^α₁ = u₁`, and otherwise `α₁ - σ`. -/
noncomputable def bookB (A : G → ProbComp (ZMod q)) (u : G) : ProbComp (Option (ZMod q)) := do
  let σ ← $ᵗ ZMod q
  let α₁ ← A (u + σ • g)
  if α₁ • g = u + σ • g then return some (α₁ - σ) else return none

/-- One attempt of `dlSelfReduce` has the law of the book's `B`. -/
theorem eval_dlSelfReduce_one_eq_bookB (A : G → ProbComp (ZMod q)) (u : G) :
    ProbComp.eval (dlSelfReduce q g A 1 u) = ProbComp.eval (bookB q g A u) := by
  have hiff (a σ : ZMod q) : (a - σ) • g = u ↔ a • g = u + σ • g := by
    rw [sub_smul, sub_eq_iff_eq_add]
  simp only [dlSelfReduce, dlRerandomize, bookB, OracleComp.retry_succ, OracleComp.retry_zero,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, hiff]

/-- CDH with only the first input masked: run `A` on `(u + ρ • g, v)` and subtract `ρ • v`. -/
noncomputable def cdhMaskFirst (A : G → G → ProbComp G) (u v : G) : ProbComp G := do
  let ρ ← $ᵗ ZMod q
  let w ← A (u + ρ • g) v
  return w - ρ • v

end General

/-! ### The group `ZMod 5` with generator `1` -/

/-- In `ZMod 5` with `g = 1`, the map `c ↦ c • g` is the identity, hence injective. -/
theorem zmod5_smul_one_injective : Function.Injective fun c : ZMod 5 => c • (1 : ZMod 5) := by
  simp only [smul_eq_mul, mul_one]
  exact Function.injective_id

/-- Returning the challenge always wins, so one attempt returns `u` with probability `1`. -/
example (u : ZMod 5) : ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) pure 1 u) (some u) = 1 := by
  have hA : dlAdvantage 5 (1 : ZMod 5) pure = 1 := by
    simp only [dlAdvantage, Experiment.succProbability, dlExperiment, ProbComp.eval_bind,
      ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one, decide_true, PMF.bind_const]
    simp [Game.succProbability]
  have h := eval_dlSelfReduce_one_smul_some 5 (1 : ZMod 5) pure u
  rwa [smul_eq_mul, mul_one, hA, ENNReal.coe_one] at h

/-- Right only on the challenge `0`, and off by one elsewhere. -/
noncomputable def zeroOnly (u : ZMod 5) : ProbComp (ZMod 5) :=
  pure (if u = 0 then 0 else u + 1)

/-- `zeroOnly` wins exactly when the challenge is `0`. -/
theorem dlAdvantage_zeroOnly : dlAdvantage 5 (1 : ZMod 5) zeroOnly = 1 / 5 := by
  have h : ∀ a : ZMod 5, (if a = 0 then 0 else a + 1) = a ↔ 0 = a := by decide
  simp only [dlAdvantage, Experiment.succProbability, dlExperiment, zeroOnly, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, smul_eq_mul, mul_one, h]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div, Nat.cast_ofNat]

/-- `zeroOnly` never returns the logarithm `3` of `3`. -/
example : ProbComp.eval (zeroOnly 3) 3 = 0 := by
  rw [zeroOnly, ProbComp.eval_pure, PMF.pure_apply, ite_eq_right (by decide)]

/-- Yet one masked call of `zeroOnly` on `3` returns `3` with probability `1 / 5`, its advantage. -/
example : ProbComp.eval (dlRerandomize 5 (1 : ZMod 5) zeroOnly 3) 3 = 1 / 5 := by
  have h := eval_dlRerandomize_smul_apply 5 (1 : ZMod 5) zeroOnly 3
  simp only [smul_eq_mul, mul_one] at h
  rw [h, ← Game.coe_succProbability_ennreal]
  change ((dlAdvantage 5 (1 : ZMod 5) zeroOnly : ℝ≥0) : ℝ≥0∞) = 1 / 5
  rw [dlAdvantage_zeroOnly, one_div, one_div, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-- And one attempt of the self-reduction on `3` returns `3` with probability `1 / 5`. -/
example : ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly 1 3) (some 3) = 1 / 5 := by
  have h := eval_dlSelfReduce_one_smul_some 5 (1 : ZMod 5) zeroOnly 3
  rw [smul_eq_mul, mul_one, dlAdvantage_zeroOnly] at h
  rw [h, one_div, one_div, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]

/-- Five attempts on `3` all fail with probability `(4 / 5) ^ 5 = 1024 / 3125`. -/
example :
    (ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly 5 3) none).toReal = 1024 / 3125 := by
  have h := eval_dlSelfReduce_smul_none 5 (1 : ZMod 5) zmod5_smul_one_injective zeroOnly 5 3
  rw [smul_eq_mul, mul_one, dlAdvantage_zeroOnly] at h
  rw [h, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le
    (ENNReal.coe_le_one_iff.2 (div_le_one_of_le₀ (by norm_num) (by norm_num)))
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  norm_num

/-- Five attempts on `3` return `3` with probability `1 - (4 / 5) ^ 5 = 2101 / 3125`. -/
example :
    (ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly 5 3) (some 3)).toReal = 2101 / 3125 := by
  have h := eval_dlSelfReduce_smul_some 5 (1 : ZMod 5) zmod5_smul_one_injective zeroOnly 5 3
  rw [smul_eq_mul, mul_one, dlAdvantage_zeroOnly] at h
  rw [h, ENNReal.toReal_sub_of_le (pow_le_one₀ (by positivity) tsub_le_self) ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_sub_of_le
    (ENNReal.coe_le_one_iff.2 (div_le_one_of_le₀ (by norm_num) (by norm_num)))
    ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat]
  norm_num

/-- `k` attempts on `3` all fail with probability at most `exp (-(k / 5))`. -/
example (k : ℕ) :
    (ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly k 3) none).toReal ≤
      Real.exp (-(k * (1 / 5 : ℝ))) := by
  have h := eval_dlSelfReduce_smul_none_le_exp_mul 5 (1 : ZMod 5) zeroOnly k 3
  rwa [smul_eq_mul, mul_one, dlAdvantage_zeroOnly, NNReal.coe_div, NNReal.coe_one,
    NNReal.coe_ofNat] at h

/-- The iteration bound with `n = 1`: `⌈1 / ε⌉ = 5` attempts fail with probability at most
`exp (-1)`. -/
example : (ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly 5 3) none).toReal ≤
    Real.exp (-1) := by
  have h := eval_dlSelfReduce_smul_none_le_exp 5 (1 : ZMod 5) zeroOnly
    (by rw [dlAdvantage_zeroOnly]; norm_num) 1 3
  rwa [dlAdvantage_zeroOnly, one_div, inv_inv, Nat.ceil_ofNat, one_mul, smul_eq_mul, mul_one,
    Nat.cast_one] at h

/-- ... and return `3` with probability at least `1 - exp (-1)`. -/
example : 1 - Real.exp (-1) ≤
    (ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) zeroOnly 5 3) (some 3)).toReal := by
  have h := one_sub_exp_le_eval_dlSelfReduce_smul_some 5 (1 : ZMod 5) zmod5_smul_one_injective
    zeroOnly (by rw [dlAdvantage_zeroOnly]; norm_num) 1 3
  rwa [dlAdvantage_zeroOnly, one_div, inv_inv, Nat.ceil_ofNat, one_mul, smul_eq_mul, mul_one,
    Nat.cast_one] at h

/-- Never right: always off by one. -/
noncomputable def offByOne (u : ZMod 5) : ProbComp (ZMod 5) :=
  pure (u + 1)

/-- `offByOne` never wins. -/
theorem dlAdvantage_offByOne : dlAdvantage 5 (1 : ZMod 5) offByOne = 0 := by
  have h : ∀ a : ZMod 5, a + 1 = a ↔ False := by decide
  simp only [dlAdvantage, Experiment.succProbability, dlExperiment, offByOne, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, smul_eq_mul, mul_one, h,
    decide_false, PMF.bind_const]
  simp [Game.succProbability]

/-- With advantage `0`, every number of attempts fails with probability `1`. -/
theorem eval_dlSelfReduce_offByOne_none (k : ℕ) (u : ZMod 5) :
    ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) offByOne k u) none = 1 := by
  have h := eval_dlSelfReduce_smul_none 5 (1 : ZMod 5) zmod5_smul_one_injective offByOne k u
  rwa [smul_eq_mul, mul_one, dlAdvantage_offByOne, ENNReal.coe_zero, tsub_zero, one_pow] at h

/-- So `eval_dlSelfReduce_smul_none_le_exp` needs `0 < ε`: here `⌈1 / ε⌉₊ = 0`, and no number of
attempts brings the failure probability down to `exp (-1)`. -/
example (k : ℕ) (u : ZMod 5) :
    ¬(ProbComp.eval (dlSelfReduce 5 (1 : ZMod 5) offByOne k u) none).toReal ≤ Real.exp (-1) := by
  rw [eval_dlSelfReduce_offByOne_none, ENNReal.toReal_one, not_le]
  exact Real.exp_lt_one_iff.2 (by norm_num)

/-! ### The group `ZMod 4` with the element `2`, of order `2` -/

/-- The constant guess `0` has advantage `1 / 4` for `g = 2` in `ZMod 4`. -/
theorem dlAdvantage_zmod4_const_zero :
    dlAdvantage 4 (2 : ZMod 4) (fun _ => pure 0) = 1 / 4 := by
  simp only [dlAdvantage, Experiment.succProbability, dlExperiment, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div, Nat.cast_ofNat]

/-- Without injectivity of `c ↦ c • 2`, `k` attempts on `0` still all fail with probability at most
`(1 - 1 / 4) ^ k`. -/
example (k : ℕ) :
    ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) (fun _ => pure 0) k 0) none ≤ (1 - 4⁻¹) ^ k := by
  have h := eval_dlSelfReduce_smul_none_le 4 (2 : ZMod 4) (fun _ => pure 0) k 0
  rwa [zero_smul, dlAdvantage_zmod4_const_zero, one_div, ENNReal.coe_inv (by norm_num),
    ENNReal.coe_ofNat] at h

/-- One attempt on `0` returns each of the two logarithms `0` and `2` of `0` with probability
`1 / 4`, so it does not fail with probability `1 - 1 / 4`: the exact failure probability of
`eval_dlSelfReduce_smul_none` needs `c ↦ c • g` injective. -/
example : ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) (fun _ => pure 0) 1 0) none ≠
    (1 - (dlAdvantage 4 (2 : ZMod 4) (fun _ => pure 0) : ℝ≥0∞)) ^ 1 := by
  set p := ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) (fun _ => pure 0) 1 0)
  have hε : (dlAdvantage 4 (2 : ZMod 4) (fun _ => pure 0) : ℝ≥0∞) = 4⁻¹ := by
    rw [dlAdvantage_zmod4_const_zero, one_div, ENNReal.coe_inv (by norm_num), ENNReal.coe_ofNat]
  have h0 : p (some 0) = 4⁻¹ := by
    have h := eval_dlSelfReduce_one_smul_some 4 (2 : ZMod 4) (fun _ => pure 0) 0
    rwa [zero_smul, hε] at h
  have h2 : p (some 2) = 4⁻¹ := by
    have h := eval_dlSelfReduce_one_smul_some 4 (2 : ZMod 4) (fun _ => pure 0) 2
    rwa [show (2 : ZMod 4) • (2 : ZMod 4) = 0 by decide, hε] at h
  have hsum : p none + (p (some 0) + p (some 2)) ≤ 1 := by
    rw [← p.tsum_coe]
    calc p none + (p (some 0) + p (some 2)) = ∑ x ∈ {none, some 0, some 2}, p x := by
          rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
            Finset.sum_singleton]
      _ ≤ ∑' x, p x := sum_le_tsum _
  intro hnone
  rw [hnone, hε, pow_one, h0, h2, ← add_assoc,
    tsub_add_cancel_of_le (ENNReal.inv_le_one.2 (by norm_num))] at hsum
  exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top (nonpos_iff_eq_zero.1
    (ENNReal.le_of_add_le_add_left ENNReal.one_ne_top (hsum.trans_eq (add_zero 1).symm)))

/-- An input outside the image of `c ↦ c • 2` makes every attempt fail. -/
example (A : ZMod 4 → ProbComp (ZMod 4)) (k : ℕ) :
    ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) A k 1) none = 1 := by
  have hne : ∀ x : ZMod 4, x • (2 : ZMod 4) ≠ 1 := by decide
  have hsome (x : ZMod 4) : some x ∉ (ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) A k 1)).support :=
    fun hx => hne x (smul_eq_of_mem_support_dlSelfReduce 4 2 hx)
  rw [PMF.apply_eq_one_iff, Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, fun y hy => ?_⟩
  · obtain ⟨y, hy⟩ := PMF.support_nonempty (ProbComp.eval (dlSelfReduce 4 (2 : ZMod 4) A k 1))
    cases y with
    | none => exact hy
    | some x => exact absurd hy (hsome x)
  · cases y with
    | none => rfl
    | some x => exact absurd hy (hsome x)

/-! ### Computational Diffie–Hellman in `ZMod 5` -/

/-- Right only when the second input is `0`, and off by one elsewhere. -/
noncomputable def secondZeroOnly (u v : ZMod 5) : ProbComp (ZMod 5) :=
  pure (if v = 0 then 0 else u * v + 1)

/-- `secondZeroOnly` wins exactly when the second exponent is `0`. -/
theorem cdhAdvantage_secondZeroOnly : cdhAdvantage 5 (1 : ZMod 5) secondZeroOnly = 1 / 5 := by
  have h : ∀ a b : ZMod 5, (if b = 0 then 0 else a * b + 1) = a * b ↔ 0 = b := by decide
  simp only [cdhAdvantage, Experiment.succProbability, cdhExperiment, secondZeroOnly,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, smul_eq_mul,
    mul_one, h, PMF.bind_const]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div, Nat.cast_ofNat]

/-- Masking both inputs succeeds with probability `1 / 5` on every input. -/
example (u v : ZMod 5) :
    ProbComp.eval (cdhSelfReduce 5 (1 : ZMod 5) secondZeroOnly u v) (u * v) = 1 / 5 := by
  have h := eval_cdhSelfReduce_smul_apply 5 (1 : ZMod 5) secondZeroOnly u v
  simp only [smul_eq_mul, mul_one] at h
  rw [h, ← Game.coe_succProbability_ennreal]
  change ((cdhAdvantage 5 (1 : ZMod 5) secondZeroOnly : ℝ≥0) : ℝ≥0∞) = 1 / 5
  rw [cdhAdvantage_secondZeroOnly, one_div, one_div, ENNReal.coe_inv (by norm_num),
    ENNReal.coe_ofNat]

/-- Masking the first input alone succeeds with probability `1` when the second input is `0`. -/
example (u : ZMod 5) :
    ProbComp.eval (cdhMaskFirst 5 (1 : ZMod 5) secondZeroOnly u 0) (u * 0) = 1 := by
  simp only [cdhMaskFirst, secondZeroOnly, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, ite_true, smul_zero, sub_zero, mul_zero,
    PMF.bind_const, PMF.pure_apply]

/-- ... and with probability `0` otherwise. -/
example (u v : ZMod 5) (hv : v ≠ 0) :
    ProbComp.eval (cdhMaskFirst 5 (1 : ZMod 5) secondZeroOnly u v) (u * v) = 0 := by
  have hout (ρ : ZMod 5) : (u + ρ • 1) * v + 1 - ρ • v = u * v + 1 := by
    simp only [smul_eq_mul, mul_one]
    ring
  have hne : u * v ≠ u * v + 1 := fun h =>
    absurd (by linear_combination -h : (1 : ZMod 5) = 0) (by decide)
  simp only [cdhMaskFirst, secondZeroOnly, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind, ite_eq_right hv, hout, PMF.bind_const, PMF.pure_apply]
  exact ite_eq_right hne

end CslibFrontierTests.Crypto.DiffieHellmanSelfReduction
