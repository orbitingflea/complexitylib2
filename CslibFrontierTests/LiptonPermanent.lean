/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Complexity.Problems.Permanent.Lipton
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases

/-! Concrete `module` clients for Lipton's random self-reduction of the permanent
(`Matrix.permanentLinePoly`, `Cslib.Complexity.liptonPermanentTrial`,
`Cslib.Complexity.liptonPermanentPlurality`) over `ZMod 5` (`n = 1`) and `ZMod 11`
(`n = 2` and `n = 3`). -/

public section

namespace CslibFrontierTests.LiptonPermanent

open scoped ENNReal Finset Matrix Polynomial
open Cslib Cslib.Code Cslib.Complexity

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 11) := ⟨by decide⟩

/-! ### 1. Univariate polynomial restriction `permanentLinePoly` over `ZMod 5` (`n = 1`) -/

/-- Explicit distinct nonzero interpolation nodes `(1, 2)` in `ZMod 5` for `n = 1`. -/
def nodesZMod5 : Fin 2 ↪ ZMod 5 where
  toFun := ![1, 2]
  inj' i j h := by
    fin_cases i <;> fin_cases j <;> revert h <;> decide

theorem nodesZMod5_ne_zero (i : Fin 2) : nodesZMod5 i ≠ 0 := by
  fin_cases i <;> decide

example (A R : Matrix (Fin 1) (Fin 1) (ZMod 5)) (t : ZMod 5) :
    (A.permanentLinePoly R).eval t = (A + t • R).permanent ∧
    (A.permanentLinePoly R).eval 0 = A.permanent ∧
    (A.permanentLinePoly R).natDegree ≤ 1 :=
  ⟨A.eval_permanentLinePoly R t,
   A.eval_zero_permanentLinePoly R,
   A.natDegree_permanentLinePoly_le R⟩

example (A R : Matrix (Fin 1) (Fin 1) (ZMod 5)) :
    lagrangeDecode nodesZMod5 (fun M : Matrix (Fin 1) (Fin 1) (ZMod 5) => M.permanent) A R =
      A.permanent :=
  lagrangeDecode_permanent nodesZMod5 A R

/-! ### 2. Single-trial Lipton self-reduction over `ZMod 5` with `n = 1` -/

/-- Query-budget and transcript-length certificates for `liptonPermanentTrial` over `ZMod 5` at
`n = 1` (`n + 1 = 2` queries). -/
example (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) :
    (liptonPermanentTrial nodesZMod5 A).IsQueryBounded 2 :=
  isQueryBounded_liptonPermanentTrial nodesZMod5 A

example {State : Type} (oracle : Matrix (Fin 1) (Fin 1) (ZMod 5) → StateT State PMF (ZMod 5))
    (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) {s s' : State} {result : ZMod 5}
    {transcript : OracleComp.Transcript (PermanentOracleSpec 1 (ZMod 5))}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (liptonPermanentTrial nodesZMod5 A) (s, [])).support) :
    transcript.length = 2 :=
  length_transcript_liptonPermanentTrial oracle nodesZMod5 A hmem

/-- Single-trial correctness over `ZMod 5` with `n = 1` (`|ZMod 5| = 5 > 3 * 1`): against any
oracle `O` erring on at most `5¹ / 3 = 1` matrix, `liptonPermanentTrial nodesZMod5 A` outputs
`A.permanent` with probability at least `1 - 2 / 3 = 1 / 3` (both in `ℝ≥0∞` and in `ℝ`). -/
theorem zmod5_n1_singleTrial (O : Matrix (Fin 1) (Fin 1) (ZMod 5) → ZMod 5)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card (ZMod 5) ^ (1 * 1) / (3 * 1))
    (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) :
    1 - ((1 : ℕ) + 1 : ℝ≥0∞) / (3 * 1 : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial nodesZMod5 A).run (fun M => pure (O M))) A.permanent ∧
    1 - ((1 : ℕ) + 1 : ℝ) / (3 * (1 : ℕ)) ≤
      (ProbComp.eval ((liptonPermanentTrial nodesZMod5 A).run (fun M => pure (O M)))
        A.permanent).toReal :=
  ⟨liptonPermanentTrial_prob_ge nodesZMod5 nodesZMod5_ne_zero O hO A,
   liptonPermanentTrial_prob_toReal_ge (by decide) nodesZMod5 nodesZMod5_ne_zero O hO A⟩

/-- Canonical `nonzeroNodes` instantiation over `ZMod 5` at `n = 1` using `3 * 1 < |ZMod 5|`. -/
theorem zmod5_n1_canonicalNodes : 3 * 1 < Fintype.card (ZMod 5) := by
  rw [ZMod.card 5]
  decide

/-- A concrete faulty oracle on `1 × 1` matrices over `ZMod 5` that corrupts `M 0 0 = 1` to `0`
and agrees with `M.permanent` on the other 4 matrices, erring on `1 ≤ 5¹ / 3` matrix. -/
def badOracle : Matrix (Fin 1) (Fin 1) (ZMod 5) → ZMod 5 :=
  fun M => if M 0 0 = 1 then 0 else M.permanent

theorem badOracle_errors_le :
    #{M | badOracle M ≠ M.permanent} ≤ Fintype.card (ZMod 5) ^ (1 * 1) / (3 * 1) := by
  rw [ZMod.card 5]
  decide

/-- Unconditional single-trial correctness against the concrete faulty oracle `badOracle`, even on
the corrupted input `!![1]` where `badOracle !![1] = 0 ≠ !![1].permanent`. -/
example (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) :
    let ν := nonzeroNodes (add_two_le_card_of_three_mul_lt (by decide) zmod5_n1_canonicalNodes)
    1 - ((1 : ℕ) + 1 : ℝ≥0∞) / (3 * 1 : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (badOracle M))) A.permanent ∧
    1 - ((1 : ℕ) + 1 : ℝ) / (3 * (1 : ℕ)) ≤
      (ProbComp.eval
        ((liptonPermanentTrial ν A).run (fun M => pure (badOracle M))) A.permanent).toReal :=
  ⟨liptonPermanentTrial_prob_ge_of_three_mul_lt (by decide) zmod5_n1_canonicalNodes
    badOracle badOracle_errors_le A,
   liptonPermanentTrial_prob_toReal_ge_of_three_mul_lt (by decide) zmod5_n1_canonicalNodes
    badOracle badOracle_errors_le A⟩

/-- Plurality amplification over `ZMod 5` at `n = 1` under the `3 * (n + 1)` error denominator:
`k` independent trials succeed with probability at least `1 - 2^{-(k / 18)}` and make `2 * k`
queries. -/
theorem zmod5_n1_plurality (k : ℕ) (O : Matrix (Fin 1) (Fin 1) (ZMod 5) → ZMod 5)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card (ZMod 5) ^ (1 * 1) / (3 * (1 + 1)))
    (A : Matrix (Fin 1) (Fin 1) (ZMod 5)) :
    (liptonPermanentPlurality k nodesZMod5 A).IsQueryBounded (k * 2) ∧
    1 - (2 : ℝ) ^ (-((k : ℝ) / 18)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k nodesZMod5 A).run (fun M => pure (O M)))
        A.permanent).toReal :=
  ⟨isQueryBounded_liptonPermanentPlurality k nodesZMod5 A,
   liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ k nodesZMod5 nodesZMod5_ne_zero O hO A⟩

/-! ### 3. Plurality amplification over `ZMod 11` for `n = 2` and `n = 3` -/

theorem zmod11_n2_card : 2 + 2 ≤ Fintype.card (ZMod 11) := by
  rw [ZMod.card 11]
  decide

theorem zmod11_n3_card : 3 * 3 < Fintype.card (ZMod 11) := by
  rw [ZMod.card 11]
  decide

/-- At `n = 2` over `ZMod 11` under `#{M | O M ≠ M.permanent} ≤ |F|⁴ / (4 * 2)`, `k` independent
trials succeed with probability at least `1 - 2^{-(k / 32)}`. -/
theorem zmod11_n2_plurality (k : ℕ) (O : Matrix (Fin 2) (Fin 2) (ZMod 11) → ZMod 11)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card (ZMod 11) ^ (2 * 2) / (4 * 2))
    (A : Matrix (Fin 2) (Fin 2) (ZMod 11)) :
    let ν := nonzeroNodes zmod11_n2_card
    1 - (2 : ℝ) ^ (-((k : ℝ) / 32)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal :=
  liptonPermanentPlurality_prob_toReal_ge_of_four_mul (by decide) k _ (nonzeroNodes_ne_zero _)
    O hO A

/-- At `n = 3` over `ZMod 11` (`|ZMod 11| = 11 > 3 * 3`) under the draft's literal
`#{M | O M ≠ M.permanent} ≤ |F|⁹ / (3 * 3)` hypothesis, `k` independent trials succeed with
probability at least `1 - 2^{-(k / 162)}`. -/
theorem zmod11_n3_plurality (k : ℕ) (O : Matrix (Fin 3) (Fin 3) (ZMod 11) → ZMod 11)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card (ZMod 11) ^ (3 * 3) / (3 * 3))
    (A : Matrix (Fin 3) (Fin 3) (ZMod 11)) :
    let ν := nonzeroNodes (add_two_le_card_of_three_mul_lt (by decide) zmod11_n3_card)
    (liptonPermanentPlurality k ν A).IsQueryBounded (k * 4) ∧
    1 - (2 : ℝ) ^ (-((k : ℝ) / 162)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal ∧
    ENNReal.ofReal (1 - (2 : ℝ) ^ (-((k : ℝ) / 162))) ≤
      ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M))) A.permanent :=
  ⟨isQueryBounded_liptonPermanentPlurality k _ A,
   liptonPermanentPlurality_prob_toReal_ge_of_three_mul_lt (by decide) zmod11_n3_card k O hO A,
   liptonPermanentPlurality_prob_ge (by decide) k _ (nonzeroNodes_ne_zero _) O hO A⟩

end CslibFrontierTests.LiptonPermanent
