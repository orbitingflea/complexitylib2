/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.SelfReduction.Family
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.PPT

/-!
# The DL and CDH self-reductions over a prime-order group family: checked instances

Clients of `CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction/Family.lean` under
module encapsulation, with ordinary imports. They apply its results, generically in the family `F`
and the group `d`, to the word-level adversary that always guesses the exponent `0`, which wins the
discrete-logarithm game in a group of order `q` with probability `1 / q`.

* The masked call, the checked loop with one attempt (the algorithm `B` of Theorem 10.2) and with
  `n * (2 * q)` attempts, and the CDH reduction of the derived CDH adversary are uniform strict
  PPT.
* The masked call is one masked call of the guess read in the group, and on every instance it is
  within `1 / 2 ^ n` of the guess's success.
* One checked attempt of the masked guess returns, on the encoding of every `α • g`, a nonempty
  word that reads as `α` with probability at least `1 / q - 1 / 2 ^ n`, although the guess itself
  is right on the instance `0` only; the same holds for `k` attempts with
  `1 - (1 - (1 / q - 1 / 2 ^ n)) ^ k`, and for the exponent that the game reads.
* With `invEps = q`, the loop with `n * (2 * q)` attempts errs with probability at most
  `(1 / 2) ^ n` once `2 * q ≤ 2 ^ n`, and the hypotheses of
  `negligible_dlSelfReduceRetryAdversary_error` hold, so it finds the discrete logarithm of every
  instance sequence in a fixed group with negligible error.
* The loop outputs the empty word or a discrete logarithm, and the empty word on every word that
  encodes no group element.
* In a fixed group the masked guess wins the worst-case game within `1 / 2 ^ n` of `1 / q`, so the
  worst-case hypotheses of `discreteLog_of_worstCase` and `cdh_of_worstCase` fail there, as the
  assumptions they imply do. The CDH reduction of the derived CDH adversary is within `2 / 2 ^ n`
  of that adversary on every pair and in the worst-case game.

`guessZero` and its two facts are private copies of the fixture in
`CslibFrontierTests/Crypto/AssumptionNonvacuity.lean`, which is not a `module` file and so cannot
be imported here.
-/

public section

namespace CslibFrontierTests.Crypto.DiffieHellmanSelfReductionFamily

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal ENNReal

variable (F : PrimeOrderGroupFamily) (d : F.Desc)

/-! ### The adversary that always guesses `0` -/

/-- Always guess the exponent `0`. -/
private noncomputable def guessZero : ℕ → F.Desc × List Bool → ProbComp (List Bool) :=
  fun _ _ => pure []

/-- Guessing `0` is uniform strict PPT: it is a constant. -/
private theorem guessZero_isPPT :
    IsPPTOn F.encDiscreteLogInput encBits
      (fun input => guessZero F input.1 input.2) :=
  (ComputableInPolyTime.const _).isPPTOn

/-- Guessing `0` against a fixed group of order `q` succeeds with probability exactly `1 / q`. -/
private theorem succProbability_discreteLogGame_guessZero (n : ℕ) :
    Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) (guessZero F) n) =
      (F.order d : ℝ≥0)⁻¹ := by
  have h := PMF.uniformOfFintype_bind_decide_eq_apply_true (0 : ZMod (F.order d))
  rw [ZMod.card] at h
  simp only [discreteLogGame, guessZero, ProbComp.eval_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.pure_bind] at h ⊢
  simp only [ofBits, List.foldr_nil, Nat.cast_zero]
  rw [Game.succProbability, h, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]

/-! ### Certificates -/

/-- The masked call of guessing `0` is uniform strict PPT. -/
example : IsPPTOn F.encDiscreteLogInput encBits
    (fun input => F.dlSelfReduceAdversary (guessZero F) input.1 input.2) :=
  F.isPPTOn_dlSelfReduceAdversary (guessZero_isPPT F)

/-- The loop with one attempt of the masked guess, the algorithm `B` of Theorem 10.2, is uniform
strict PPT. -/
example : IsPPTOn F.encDiscreteLogInput encBits
    (fun input => F.dlSelfReduceRetryAdversary (guessZero F) (fun _ => 1) input.1 input.2) :=
  F.isPPTOn_dlSelfReduceRetryAdversary (guessZero_isPPT F) (k := fun _ => 1) (by fun_prop)

/-- The loop with `n * (2 * q)` attempts of the masked guess is uniform strict PPT. -/
example : IsPPTOn F.encDiscreteLogInput encBits
    (fun input => F.dlSelfReduceRetryAdversary (guessZero F) (fun n => n * (2 * F.order d))
      input.1 input.2) :=
  F.isPPTOn_dlSelfReduceRetryAdversary_invEps (guessZero_isPPT F) (invEps := fun _ => F.order d)
    (by fun_prop)

/-- The CDH reduction of the CDH adversary derived from guessing `0` is uniform strict PPT. -/
example : (F.cdhSelfReduceAdversary (F.dlToCDHAdversary (guessZero F))).IsPPT :=
  F.isPPT_cdhSelfReduceAdversary (F.isPPT_dlToCDHAdversary (guessZero_isPPT F))

/-! ### One masked call -/

/-- On the encoding of `u`, the masked guess is one masked call of the guess read in the group. -/
example (n : ℕ) (u : F.Carrier d) :
    F.discreteLogAdversary (F.dlSelfReduceAdversary (guessZero F)) n d u = do
      let σ ← F.sampleExp n d
      let α₁ ← F.discreteLogAdversary (guessZero F) n d
        (u + (σ : ZMod (F.order d)) • F.generator d)
      return α₁ - (σ : ZMod (F.order d)) :=
  F.discreteLogAdversary_dlSelfReduceAdversary (guessZero F) n d u

/-- On every instance, the masked guess returns the exponent within `1 / 2 ^ n` of the guess's
success in the group. -/
example (n : ℕ) (α : ZMod (F.order d)) :
    Experiment.advantage
      ((fun x => decide (x = α)) <$>
        F.discreteLogAdversary (F.dlSelfReduceAdversary (guessZero F)) n d (α • F.generator d))
      (dlExperiment (F.order d) (F.generator d) (F.discreteLogAdversary (guessZero F) n d)) ≤
      1 / 2 ^ n :=
  F.advantage_dlSelfReduceAdversary_le (guessZero F) n d α

/-! ### Every instance -/

/-- **Theorem 10.2 on words**: one checked attempt of the masked guess returns, on the encoding of
every `α • g`, a nonempty word that reads as `α` with probability at least `1 / q - 1 / 2 ^ n`,
although guessing `0` is right on one instance only. At `α = 0` the empty word, the book's `fail`,
does not count. -/
example (n : ℕ) (α : ZMod (F.order d)) :
    (((F.order d : ℝ≥0)⁻¹ - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤
      (ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) (fun _ => 1) n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} := by
  have h := F.le_toOuterMeasure_dlSelfReduceRetryAdversary_one (guessZero F) n d α
  rwa [← F.succProbability_discreteLogGame_pure, succProbability_discreteLogGame_guessZero] at h

/-- `k` checked attempts of the masked guess return a nonempty word that reads as `α` with
probability at least `1 - (1 - (1 / q - 1 / 2 ^ n)) ^ k`. -/
example (k : ℕ → ℕ) (n : ℕ) (α : ZMod (F.order d)) :
    1 - (1 - (((F.order d : ℝ≥0)⁻¹ - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) ^ k n ≤
      (ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) k n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} := by
  have h := F.one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary (guessZero F) k n d α
  rwa [← F.succProbability_discreteLogGame_pure, succProbability_discreteLogGame_guessZero] at h

/-- The game reads the answer of one checked attempt as `α` with at least the same probability. -/
example (n : ℕ) (α : ZMod (F.order d)) :
    (((F.order d : ℝ≥0)⁻¹ - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤
      ProbComp.eval (F.discreteLogAdversary (F.dlSelfReduceRetryAdversary (guessZero F) fun _ => 1)
        n d (α • F.generator d)) α := by
  have h := F.le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one (guessZero F) n d α
  rwa [← F.succProbability_discreteLogGame_pure, succProbability_discreteLogGame_guessZero] at h

/-- ... and the answer of `k` checked attempts. -/
example (k : ℕ → ℕ) (n : ℕ) (α : ZMod (F.order d)) :
    1 - (1 - (((F.order d : ℝ≥0)⁻¹ - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) ^ k n ≤
      ProbComp.eval (F.discreteLogAdversary (F.dlSelfReduceRetryAdversary (guessZero F) k) n d
        (α • F.generator d)) α := by
  have h := F.one_sub_pow_le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary (guessZero F) k
    n d α
  rwa [← F.succProbability_discreteLogGame_pure, succProbability_discreteLogGame_guessZero] at h

/-- With `invEps = q` and `2 * q ≤ 2 ^ n`, the loop with `n * (2 * q)` attempts of the masked
guess errs on the encoding of every `α • g` with probability at most `(1 / 2) ^ n`. -/
example (n : ℕ) (α : ZMod (F.order d)) (hn : 2 * F.order d ≤ 2 ^ n) :
    ((ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) (fun n => n * (2 * F.order d)) n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out = [] ∨ (ofBits out : ZMod (F.order d)) ≠ α}).toReal ≤ (1 / 2 : ℝ) ^ n :=
  F.dlSelfReduceRetryAdversary_error_le_pow (guessZero F) (fun _ => F.order d) n d α
    (by rw [succProbability_discreteLogGame_guessZero]; simp)
    (show 1 / (2 ^ n : ℝ) ≤ 1 / (2 * (F.order d : ℝ)) from
      one_div_le_one_div_of_le (mul_pos two_pos (by exact_mod_cast (F.prime_order d).pos))
        (by exact_mod_cast hn))

/-- ... so the game reads an exponent other than `α` with probability at most `(1 / 2) ^ n`. -/
example (n : ℕ) (α : ZMod (F.order d)) (hn : 2 * F.order d ≤ 2 ^ n) :
    ((ProbComp.eval (F.discreteLogAdversary
        (F.dlSelfReduceRetryAdversary (guessZero F) fun n => n * (2 * F.order d)) n d
        (α • F.generator d))).toOuterMeasure {x | x ≠ α}).toReal ≤ (1 / 2 : ℝ) ^ n :=
  F.discreteLogAdversary_dlSelfReduceRetryAdversary_error_le_pow (guessZero F) (fun _ => F.order d)
    n d α (by rw [succProbability_discreteLogGame_guessZero]; simp)
    (show 1 / (2 ^ n : ℝ) ≤ 1 / (2 * (F.order d : ℝ)) from
      one_div_le_one_div_of_le (mul_pos two_pos (by exact_mod_cast (F.prime_order d).pos))
        (by exact_mod_cast hn))

/-- The hypotheses of `negligible_dlSelfReduceRetryAdversary_error` hold for guessing `0` with
`invEps = q`: the loop is a random search that errs with negligible probability on every sequence
of instances in a fixed group. -/
example (α : ℕ → ZMod (F.order d)) :
    Negligible fun n =>
      ((ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) (fun n => n * (2 * F.order d)) n
        (d, F.encode d (α n • F.generator d)))).toOuterMeasure
        {out | out = [] ∨ (ofBits out : ZMod (F.order d)) ≠ α n}).toNNReal :=
  F.negligible_dlSelfReduceRetryAdversary_error (adversary := guessZero F)
    (invEps := fun _ => F.order d) (by fun_prop) (fun _ => d) α
    (Filter.Eventually.of_forall fun _ => (F.prime_order d).pos)
    (Filter.Eventually.of_forall fun n => by
      rw [succProbability_discreteLogGame_guessZero]
      simp)

/-- ... so the game reads an exponent other than `α n` with negligible probability. -/
example (α : ℕ → ZMod (F.order d)) :
    Negligible fun n =>
      ((ProbComp.eval (F.discreteLogAdversary
        (F.dlSelfReduceRetryAdversary (guessZero F) fun n => n * (2 * F.order d)) n d
        (α n • F.generator d))).toOuterMeasure {x | x ≠ α n}).toNNReal :=
  F.negligible_discreteLogAdversary_dlSelfReduceRetryAdversary_error (adversary := guessZero F)
    (invEps := fun _ => F.order d) (by fun_prop) (fun _ => d) α
    (Filter.Eventually.of_forall fun _ => (F.prime_order d).pos)
    (Filter.Eventually.of_forall fun n => by
      rw [succProbability_discreteLogGame_guessZero]
      simp)

/-- On every input word, the loop of the masked guess outputs the empty word or a word whose
exponent passes the test. -/
example {k : ℕ → ℕ} {n : ℕ} {w out : List Bool}
    (hout : out ∈ (ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) k n (d, w))).support) :
    out = [] ∨ F.encode d ((ofBits out : ZMod (F.order d)) • F.generator d) = w :=
  F.eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary hout

/-- The loop of the masked guess outputs the empty word or a discrete logarithm of its input. -/
example {k : ℕ → ℕ} {n : ℕ} {u : F.Carrier d} {out : List Bool}
    (hout : out ∈ (ProbComp.eval
      (F.dlSelfReduceRetryAdversary (guessZero F) k n (d, F.encode d u))).support) :
    out = [] ∨ (ofBits out : ZMod (F.order d)) • F.generator d = u :=
  F.eq_nil_or_smul_eq_of_mem_support_dlSelfReduceRetryAdversary hout

/-- On a word that encodes no element, the loop outputs the empty word. -/
example {k : ℕ → ℕ} {n : ℕ} {w out : List Bool} (hw : w ∉ Set.range (F.encode d))
    (hout : out ∈ (ProbComp.eval (F.dlSelfReduceRetryAdversary (guessZero F) k n (d, w))).support) :
    out = [] :=
  F.eq_nil_of_mem_support_dlSelfReduceRetryAdversary_of_not_mem_range hw hout

/-! ### Worst case in a fixed group -/

/-- For every setup law, the masked guess wins the worst-case game within `1 / 2 ^ n` of the
guess's success in the average-case game. -/
example (setup : ℕ → PMF F.Desc) (α : ∀ d : F.Desc, ZMod (F.order d)) (n : ℕ) :
    Game.advantage (F.dlWorstCaseGame setup α (F.dlSelfReduceAdversary (guessZero F)) n)
      (F.discreteLogGame setup (guessZero F) n) ≤ 1 / 2 ^ n :=
  F.advantage_dlWorstCaseGame_discreteLogGame_le setup α (guessZero F) n

/-- In a fixed group, the masked guess wins the worst-case game on any instances within
`1 / 2 ^ n` of `1 / q`. -/
example (α : ∀ d : F.Desc, ZMod (F.order d)) (n : ℕ) :
    (F.order d : ℝ≥0)⁻¹ ≤
      Game.succProbability (F.dlWorstCaseGame (fun _ => PMF.pure d) α
        (F.dlSelfReduceAdversary (guessZero F)) n) + 1 / 2 ^ n := by
  rw [← succProbability_discreteLogGame_guessZero F d n]
  exact F.succProbability_discreteLogGame_le_dlWorstCaseGame _ α _ n

/-- The worst-case hypothesis of `discreteLog_of_worstCase` fails for a fixed group, as
`DiscreteLog` does: some PPT adversary wins the worst-case game with non-negligible probability
on every family of instances. -/
theorem not_dlWorstCase_const :
    ¬ ∀ adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool),
      IsPPTOn F.encDiscreteLogInput encBits (fun input => adversary input.1 input.2) →
      ∃ α : ∀ d : F.Desc, ZMod (F.order d), Negligible fun n =>
        Game.succProbability (F.dlWorstCaseGame (fun _ => PMF.pure d) α adversary n) := by
  intro hworst
  have hneg := F.discreteLog_of_worstCase hworst (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

/-- On every pair, the CDH reduction of the CDH adversary derived from guessing `0` is within
`2 / 2 ^ n` of that adversary's success in the group. -/
example (n : ℕ) (α β : ZMod (F.order d)) :
    Experiment.advantage
      ((fun w => decide (w = (α * β) • F.generator d)) <$>
        F.cdhSelfReduceAdversary (F.dlToCDHAdversary (guessZero F)) n d (α • F.generator d)
          (β • F.generator d))
      (cdhExperiment (F.order d) (F.generator d) (F.dlToCDHAdversary (guessZero F) n d)) ≤
      2 / 2 ^ n :=
  F.advantage_cdhSelfReduceAdversary_le _ n d α β

/-- For every setup law, the CDH reduction wins the worst-case game within `2 / 2 ^ n` of the
derived adversary's success in the average-case game. -/
example (setup : ℕ → PMF F.Desc) (α β : ∀ d : F.Desc, ZMod (F.order d)) (n : ℕ) :
    Game.advantage
      (F.cdhWorstCaseGame setup α β (F.cdhSelfReduceAdversary (F.dlToCDHAdversary (guessZero F))) n)
      (F.cdhGame setup (F.dlToCDHAdversary (guessZero F)) n) ≤ 2 / 2 ^ n :=
  F.advantage_cdhWorstCaseGame_cdhGame_le setup α β _ n

/-- ... so the derived adversary's average-case success is at most the reduction's worst-case
success plus `2 / 2 ^ n`. -/
example (setup : ℕ → PMF F.Desc) (α β : ∀ d : F.Desc, ZMod (F.order d)) (n : ℕ) :
    Game.succProbability (F.cdhGame setup (F.dlToCDHAdversary (guessZero F)) n) ≤
      Game.succProbability (F.cdhWorstCaseGame setup α β
        (F.cdhSelfReduceAdversary (F.dlToCDHAdversary (guessZero F))) n) + 2 / 2 ^ n :=
  F.succProbability_cdhGame_le_cdhWorstCaseGame setup α β _ n

/-- The worst-case hypothesis of `cdh_of_worstCase` fails for a fixed group, as `CDH` does. -/
theorem not_cdhWorstCase_const :
    ¬ ∀ adversary : F.CDHAdversary, adversary.IsPPT →
      ∃ α β : ∀ d : F.Desc, ZMod (F.order d), Negligible fun n =>
        Game.succProbability (F.cdhWorstCaseGame (fun _ => PMF.pure d) α β adversary n) := by
  intro hworst
  have hneg := (F.cdh_of_worstCase hworst).discreteLog (guessZero F) (guessZero_isPPT F)
  simp only [succProbability_discreteLogGame_guessZero] at hneg
  exact not_negligible_const (inv_ne_zero (Nat.cast_ne_zero.mpr (F.prime_order d).ne_zero)) hneg

end CslibFrontierTests.Crypto.DiffieHellmanSelfReductionFamily
