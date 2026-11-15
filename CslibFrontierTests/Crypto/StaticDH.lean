/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.DiffieHellman.Static
import CslibFrontier.Languages.Probabilistic.QueryCount.Congr
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Static Diffie–Hellman and ElGamal key recovery: checked instances and probes

Concrete checks for `CslibFrontier/Crypto/Computational/DiffieHellman/Static.lean` under module
encapsulation:

* In any `ZMod q`-module `G`, every 0-query static-DH adversary wins `sdhExperiment` with
  probability `1 / q` (`sdhAdvantage_of_isQueryBounded_zero`).
* In `ZMod 5` with generator `1`, the 1-query SDH adversary `queryOneSDH 5` wins with probability
  `1`, and `sdhToElGamalKeyRecovery` turns it into a 1-query ElGamal key-recovery adversary with
  advantage `1` whose queries all have second component `0`; `dlToSDH` and
  `elGamalKeyRecoveryToSDH` preserve advantages and query budgets on concrete instances.
* Probe 1 shows that negating the first ciphertext component (`(-v, 0)` for `(1 / v, 1)`) is
  essential: querying `(v, 0)` instead returns a different reply from `sdhOracle` at `α = 1, v = 1`
  and drops the advantage of `queryOneSDH 5` from `1` to `1 / 5`.
* Probe 2 shows that the `+ 1` query in `isQueryBounded_elGamalKeyRecoveryToSDH` (`Q + 1`) is
  needed because `ElGamalKeyRecoveryAdversary` receives the public key `α • g` whereas
  `SDHAdversary` receives no initial group element: `zeroQueryKeyRecovery` makes `0` decryption
  queries and wins with probability `1` (and `elGamalKeyRecoveryToSDH 1` turns it into a 1-query
  SDH adversary with advantage `1`), whereas every 0-query SDH adversary in `ZMod 5` wins with
  probability `1 / 5 ≠ 1`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.StaticDH

open Cslib Cslib.Probability Cslib.Crypto
open scoped NNReal ENNReal

section General

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G]

/-- Every 0-query SDH adversary in a `ZMod q`-module wins with probability `1 / q`. -/
private theorem sdhAdvantage_of_isQueryBounded_zero (A : SDHAdversary G q)
    (h : A.IsQueryBounded 0) :
    sdhAdvantage q A = (q : ℝ≥0)⁻¹ := by
  classical
  have hno : A.QueriesSatisfy fun _ => False :=
    OracleComp.IsCostBounded.of_le h fun r => by cases r <;> simp
  have hrun (α : ZMod q) : ProbComp.eval (A.run (sdhOracle q α)) =
      ProbComp.eval (A.run (sdhOracle q 0)) :=
    hno.eval_run_congr fun _ hq => hq.elim
  simp only [sdhAdvantage, Experiment.succProbability, sdhExperiment, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, hrun]
  rw [Game.succProbability, PMF.bind_comm, PMF.bind_apply]
  simp only [PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card]
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, ENNReal.toNNReal_inv,
    ENNReal.toNNReal_natCast]

end General

/-! ### Concrete checks in `ZMod 5` with generator `1` -/

/-- The 1-query SDH adversary in `ZMod q` that queries `1` and returns the reply `α • 1 = α`. -/
private def queryOneSDH (q : ℕ) : SDHAdversary (ZMod q) q :=
  ProbOracleComp.query (spec := SDHSpec (ZMod q)) 1

private theorem isQueryBounded_queryOneSDH (q : ℕ) : (queryOneSDH q).IsQueryBounded 1 :=
  ProbOracleComp.IsQueryBounded.query 1

private theorem sdhAdvantage_queryOneSDH (q : ℕ) [NeZero q] :
    sdhAdvantage q (queryOneSDH q) = 1 := by
  simp only [sdhAdvantage, Experiment.succProbability, sdhExperiment, queryOneSDH,
    ProbOracleComp.run_query, sdhOracle, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    smul_eq_mul, mul_one, decide_true, PMF.bind_const]
  simp [Game.succProbability]

-- In `ZMod 5` with generator `1`, `sdhToElGamalKeyRecovery (queryOneSDH 5)` recovers the secret
-- key with probability `1` using `1` decryption query, and its converse `elGamalKeyRecoveryToSDH`
-- has SDH advantage `1` with budget `2 = 1 + 1`.
example :
    elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (sdhToElGamalKeyRecovery (queryOneSDH 5)) = 1 ∧
      sdhAdvantage 5
        (elGamalKeyRecoveryToSDH (1 : ZMod 5) (sdhToElGamalKeyRecovery (queryOneSDH 5))) = 1 ∧
      (elGamalKeyRecoveryToSDH (1 : ZMod 5)
        (sdhToElGamalKeyRecovery (queryOneSDH 5))).IsQueryBounded 2 ∧
      ∀ u : ZMod 5, (sdhToElGamalKeyRecovery (queryOneSDH 5) u).IsQueryBounded 1 ∧
        (sdhToElGamalKeyRecovery (queryOneSDH 5) u).QueriesSatisfy (fun ct => ct.2 = 0) :=
  ⟨by rw [elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery, sdhAdvantage_queryOneSDH],
    by rw [sdhAdvantage_elGamalKeyRecoveryToSDH,
        elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery, sdhAdvantage_queryOneSDH],
    isQueryBounded_elGamalKeyRecoveryToSDH (1 : ZMod 5)
      (isQueryBounded_sdhToElGamalKeyRecovery (isQueryBounded_queryOneSDH 5)),
    fun u => ⟨isQueryBounded_sdhToElGamalKeyRecovery (isQueryBounded_queryOneSDH 5) u,
      queriesSatisfy_sdhToElGamalKeyRecovery (queryOneSDH 5) u⟩⟩

-- In `ZMod 5`, `dlToSDH 1 pure` wins `sdhExperiment` with probability `1` and makes `1` query.
example :
    sdhAdvantage 5 (dlToSDH (1 : ZMod 5) pure) = 1 ∧
      (dlToSDH (1 : ZMod 5) pure).IsQueryBounded 1 ∧
      (dlToSDH (1 : ZMod 5) pure).QueriesSatisfy (· = (1 : ZMod 5)) := by
  refine ⟨?_, isQueryBounded_dlToSDH 1 pure, queriesSatisfy_dlToSDH 1 pure⟩
  simp only [sdhAdvantage_dlToSDH, dlAdvantage, Experiment.succProbability, dlExperiment,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one, decide_true,
    PMF.bind_const]
  simp [Game.succProbability]

/-! ### Probes for algebraic choice and query budget -/

-- Probe 1: negating the first ciphertext component (`(-v, 0)` for `(1 / v, 1)`) is essential.
-- Without negation, querying `(v, 0)` returns `-(α • v)` instead of `α • v` (`α = 1, v = 1`),
-- and a reduction querying `(v, 0)` on `queryOneSDH 5` wins only when `-α = α` (`α = 0`), with
-- probability `1 / 5` instead of `1`.
example :
    ProbComp.eval (elGamalDecryptOracle 5 (1 : ZMod 5) ((1 : ZMod 5), (0 : ZMod 5))) ≠
      ProbComp.eval (sdhOracle 5 (1 : ZMod 5) (1 : ZMod 5)) := by
  intro h
  have h1 := congrArg (fun p => p (1 : ZMod 5)) h
  have hne : (1 : ZMod 5) ≠ -1 := by decide
  simp [elGamalDecryptOracle, sdhOracle, hne] at h1

/-- A faulty key-recovery reduction that queries `(v, 0)` without negating `v`. -/
private def unnegatedReduction {q : ℕ} {G : Type} [AddCommGroup G] (A : SDHAdversary G q) :
    ElGamalKeyRecoveryAdversary G q :=
  fun _ => ProbOracleComp.simulate (fun v => ProbOracleComp.query (v, 0)) A

example :
    elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) (unnegatedReduction (queryOneSDH 5)) = 1 / 5 := by
  have hiff (α : ZMod 5) : (-α = α) ↔ (0 : ZMod 5) = α := by decide +revert
  simp only [elGamalKeyRecoveryAdvantage, Experiment.succProbability, elGamalKeyRecoveryExperiment,
    unnegatedReduction, queryOneSDH, ProbOracleComp.run_simulate, ProbOracleComp.run_query,
    elGamalDecryptOracle, zero_sub, smul_eq_mul, mul_one,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.pure_bind, hiff]
  rw [Game.succProbability, PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card,
    ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast, one_div, Nat.cast_ofNat]

-- Probe 2: the extra query in `isQueryBounded_elGamalKeyRecoveryToSDH` (`Q + 1`) is needed
-- because `ElGamalKeyRecoveryAdversary` receives the public key `u = α • g` as input whereas
-- `SDHAdversary` receives no input: in `ZMod 5`, `zeroQueryKeyRecovery` makes `0` decryption
-- queries and wins with probability `1` (and `elGamalKeyRecoveryToSDH 1` turns it into a 1-query
-- SDH adversary with advantage `1`), whereas every 0-query SDH adversary in `ZMod 5` has
-- advantage `1 / 5 ≠ 1`.
private def zeroQueryKeyRecovery : ElGamalKeyRecoveryAdversary (ZMod 5) 5 :=
  fun u => pure u

example :
    (∀ u : ZMod 5, (zeroQueryKeyRecovery u).IsQueryBounded 0) ∧
      elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) zeroQueryKeyRecovery = 1 ∧
      (elGamalKeyRecoveryToSDH (1 : ZMod 5) zeroQueryKeyRecovery).IsQueryBounded 1 ∧
      sdhAdvantage 5 (elGamalKeyRecoveryToSDH (1 : ZMod 5) zeroQueryKeyRecovery) = 1 ∧
      ∀ A : SDHAdversary (ZMod 5) 5, A.IsQueryBounded 0 →
        sdhAdvantage 5 A = 1 / 5 ∧ sdhAdvantage 5 A ≠ 1 := by
  have hwin : elGamalKeyRecoveryAdvantage 5 (1 : ZMod 5) zeroQueryKeyRecovery = 1 := by
    simp only [elGamalKeyRecoveryAdvantage, Experiment.succProbability,
      elGamalKeyRecoveryExperiment, zeroQueryKeyRecovery, ProbOracleComp.run_pure,
      ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind, smul_eq_mul, mul_one, decide_true,
      PMF.bind_const]
    simp [Game.succProbability]
  refine ⟨fun u => OracleComp.IsCostBounded.pure u 0, hwin,
    isQueryBounded_elGamalKeyRecoveryToSDH (1 : ZMod 5)
      (fun u => OracleComp.IsCostBounded.pure u 0),
    by rw [sdhAdvantage_elGamalKeyRecoveryToSDH, hwin],
    fun A hA => ?_⟩
  have hAeq : sdhAdvantage 5 A = 1 / 5 := by
    rw [sdhAdvantage_of_isQueryBounded_zero 5 A hA, one_div, Nat.cast_ofNat]
  refine ⟨hAeq, ?_⟩
  rw [hAeq]
  norm_num

end CslibFrontierTests.Crypto.StaticDH
