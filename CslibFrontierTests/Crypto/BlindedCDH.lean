/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.DiffieHellman.BlindedFamily
import CslibFrontier.Crypto.Computational.DiscreteLog.SchnorrGroup
import CslibFrontier.Crypto.Negligible.Basic
import Mathlib.Tactic.NormNum.Prime

/-!
# The blinded Diffie–Hellman problems: checked instances

An ordinary `module` client of `CslibFrontier.Crypto.Computational.DiffieHellman.Blinded` and
`CslibFrontier.Crypto.Computational.DiffieHellman.BlindedFamily` ([BonehShoup2023], Lemmas 21.7
and 21.8).

* In `ZMod 7` with `g = 1`, the blinded value has the closed form of `blindedDH_smul_smul`, and the
  reductions' `solve` recovers the Diffie–Hellman value from right answers (through
  `BlindedCDHAnswer.solve_eq_iff` and `BlindedCDHPairAnswer.solve_eq`) and not from a wrong one.
  Both hypotheses of `BlindedCDHPairAnswer.solve_eq` are needed: with equal exponents `solve`
  returns `0`, and in `ZMod 4`, for every blinding exponent, no scalar multiple of
  `value₂ - value₁` in place of the inverse gives the target.
* In `ZMod 5` with `g = 1`, adversaries that always win the two problems are turned into CDH
  solvers that always win.
* Over any prime-order group family, the two games unfold to the fixed-group experiments, the two
  PPT predicates are satisfied by adversaries that copy an input element, the two certificates
  and the two loss bounds apply to them, and the two theorems are used as a client would,
  including on Schnorr groups.
-/

public section

namespace CslibFrontierTests.Crypto.BlindedCDH

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

/-! ### The algebra in `ZMod 7` with `g = 1` -/

/-- Lemma 21.7 at `μ = 2`, `ν = 3`, `x = 4`, `y = 5`, `γ = 6`: the blinded value is `6`. -/
example :
    blindedDH (q := 7) (2 : ZMod 7) 4 6 ((3 : ZMod 7) • (1 : ZMod 7)) ((5 : ZMod 7) • 1) = 6 := by
  decide

/-- The same value in the form `((x - γ * μ) * (y - γ * ν)) • g` of `blindedDH_smul_smul`. -/
example : blindedDH (q := 7) (2 : ZMod 7) 4 6 ((3 : ZMod 7) • (1 : ZMod 7)) ((5 : ZMod 7) • 1) =
    (((4 : ZMod 7) - 6 * 2) * (5 - 6 * 3)) • 1 :=
  blindedDH_smul_smul 1 2 3 4 5 6

/-- From the right value the reduction returns `x * y = 6`, by `BlindedCDHAnswer.solve_eq_iff`. -/
example : (⟨6, 6⟩ : BlindedCDHAnswer 7 (ZMod 7)).solve 1 2 3 ((4 : ZMod 7) • 1) ((5 : ZMod 7) • 1) =
    ((4 * 5 : ZMod 7)) • 1 :=
  (BlindedCDHAnswer.solve_eq_iff _ 1 2 3 4 5).mpr (by decide)

/-- From a wrong value it does not. -/
example : (⟨6, 0⟩ : BlindedCDHAnswer 7 (ZMod 7)).solve 1 2 3 ((4 : ZMod 7) • 1) ((5 : ZMod 7) • 1) ≠
    ((4 * 5 : ZMod 7)) • 1 := by
  decide

/-- The answer of Lemma 21.8 at `μ = 2`, `β = 3`, `x = 4`, exponents `1` and `5`, `v = 6`. -/
def pairAnswer7 : BlindedCDHPairAnswer 7 (ZMod 7) where
  exponent₁ := 1
  exponent₂ := 5
  right := 6
  value₁ := 6
  value₂ := 5

/-- `7` is prime. -/
local instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- Both values are the blinded ones, so the reduction returns `β * x = 5`. -/
example : pairAnswer7.solve 2 ((3 : ZMod 7) • (1 : ZMod 7)) = ((3 * 4 : ZMod 7)) • 1 :=
  pairAnswer7.solve_eq 1 2 3 4 (by decide) (by decide) (by decide)

/-- The hypothesis `exponent₁ ≠ exponent₂` is needed: with both exponents `1` and both values the
blinded one, the reduction returns `0`, not `β * x = 5`. -/
example :
    let out : BlindedCDHPairAnswer 7 (ZMod 7) := ⟨1, 1, 6, 6, 6⟩
    out.value₁ = blindedDH (2 : ZMod 7) 4 out.exponent₁ ((3 : ZMod 7) • (1 : ZMod 7)) out.right ∧
      out.solve 2 ((3 : ZMod 7) • (1 : ZMod 7)) = 0 ∧ ((3 * 4 : ZMod 7)) • (1 : ZMod 7) ≠ 0 := by
  decide

/-- Primality is needed: in `ZMod 4` with `β = 1`, `x = 1`, `v = 0` and exponents `0`, `2`, for
every blinding exponent `μ` the two blinded values are `0` and `2` and the target is `1`, and the
formula of `solve` with any scalar `c` in place of `(γ₁ - γ₂)⁻¹` never gives `1`. -/
example :
    ∀ μ c : ZMod 4,
      blindedDH (q := 4) μ 1 0 ((1 : ZMod 4) • (1 : ZMod 4)) 0 = 0 ∧
      blindedDH (q := 4) μ 1 2 ((1 : ZMod 4) • (1 : ZMod 4)) 0 = 2 ∧
      c • ((2 : ZMod 4) - 0) - μ • (0 : ZMod 4) + ((0 + 2) * μ) • ((1 : ZMod 4) • (1 : ZMod 4)) ≠
        ((1 * 1 : ZMod 4)) • 1 := by
  decide

/-! ### The experiments in `ZMod 5` with `g = 1` -/

/-- In `ZMod 5` with `g = 1` every element is its own exponent, so the Diffie–Hellman element of
`u` and `v` is their product: answer with exponent `0`. -/
noncomputable def productAdversary (_a _b u v : ZMod 5) : ProbComp (BlindedCDHAnswer 5 (ZMod 5)) :=
  pure ⟨0, u * v⟩

/-- `productAdversary` always wins the blinded experiment. -/
theorem blindedCDHAdvantage_productAdversary :
    blindedCDHAdvantage 5 (1 : ZMod 5) productAdversary = 1 := by
  simp only [blindedCDHAdvantage, Experiment.succProbability, blindedCDHExperiment,
    productAdversary, blindedDH, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    smul_eq_mul, mul_one, zero_mul, sub_zero, decide_true, PMF.bind_const]
  simp [Game.succProbability]

/-- So the reduction of Lemma 21.7 always solves its CDH instance. -/
example : cdhAdvantage 5 (1 : ZMod 5) (blindedCDHToCDH 5 1 productAdversary) = 1 := by
  rw [cdhAdvantage_blindedCDHToCDH, blindedCDHAdvantage_productAdversary]

/-- `5` is prime. -/
local instance fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- For Lemma 21.8 in `ZMod 5`: exponents `0` and `1`, `v = 0`, values `0` and `-(u - a) * b`. -/
noncomputable def pairAdversary (a b u : ZMod 5) : ProbComp (BlindedCDHPairAnswer 5 (ZMod 5)) :=
  pure ⟨0, 1, 0, 0, -((u - a) * b)⟩

/-- `pairAdversary` always wins the two-point blinded experiment. -/
theorem blindedCDHPairAdvantage_pairAdversary :
    blindedCDHPairAdvantage 5 (1 : ZMod 5) pairAdversary = 1 := by
  have h (α β x : ZMod 5) : ((0 : ZMod 5) ≠ 1 ∧ (0 : ZMod 5) = (x - 0 * α) * (0 - 0 * β) ∧
      -((x - α) * β) = (x - 1 * α) * (0 - 1 * β)) ↔ True :=
    iff_true_intro ⟨by decide, by ring, by ring⟩
  simp only [blindedCDHPairAdvantage, Experiment.succProbability, blindedCDHPairExperiment,
    pairAdversary, blindedDH, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind,
    smul_eq_mul, mul_one, h, decide_true, PMF.bind_const]
  simp [Game.succProbability]

/-- So the reduction of Lemma 21.8 always solves its CDH instance. -/
example : 1 ≤ cdhAdvantage 5 (1 : ZMod 5) (blindedCDHPairToCDH 5 1 pairAdversary) :=
  blindedCDHPairAdvantage_pairAdversary ▸ blindedCDHPairAdvantage_le_cdhAdvantage 5 1 pairAdversary

/-! ### The family layer -/

section Family

variable (F : PrimeOrderGroupFamily)

/-- The blinded CDH game is the fixed-group experiment after the setup draw. -/
example (setup : ℕ → PMF F.Desc) (adversary : F.BlindedCDHAdversary) (n : ℕ) :
    F.blindedCDHGame setup adversary n = Game.withSetup (setup n) fun d =>
      blindedCDHExperiment (F.order d) (F.generator d) (adversary n d) :=
  rfl

/-- The two-point blinded CDH game is the fixed-group experiment after the setup draw. -/
example (setup : ℕ → PMF F.Desc) (adversary : F.BlindedCDHPairAdversary) (n : ℕ) :
    F.blindedCDHPairGame setup adversary n = Game.withSetup (setup n) fun d =>
      blindedCDHPairExperiment (F.order d) (F.generator d) (adversary n d) :=
  rfl

/-- The blinded CDH adversary that answers exponent `0` and its input `u`. -/
noncomputable def copyBlindedAdversary : F.BlindedCDHAdversary :=
  fun _ _ _ _ u _ => pure ⟨0, u⟩

/-- `copyBlindedAdversary` is uniform strict PPT, so `BlindedCDHAdversary.IsPPT` is satisfiable
in every family. -/
theorem copyBlindedAdversary_isPPT : (copyBlindedAdversary F).IsPPT := by
  refine ((ComputableInPolyTime.const (0 : ℕ)).prod
    (F.encBlindedCDHInput_leftPublic_polyTime .id')).isPPTOn.congr fun x => ?_
  simp [copyBlindedAdversary]

/-- The certified reduction of Lemma 21.7 at this adversary. -/
example : (F.blindedCDHToCDHAdversary (copyBlindedAdversary F)).IsPPT :=
  isPPT_blindedCDHToCDHAdversary (copyBlindedAdversary_isPPT F)

/-- The sampling loss of Lemma 21.7 at this adversary. -/
example (setup : ℕ → PMF F.Desc) (n : ℕ) :
    Game.advantage (F.blindedCDHGame setup (copyBlindedAdversary F) n)
      (F.cdhGame setup (F.blindedCDHToCDHAdversary (copyBlindedAdversary F)) n) ≤ 2 / 2 ^ n :=
  F.advantage_blindedCDHGame_cdhGame_le setup _ n

/-- Lemma 21.7 applied as a client would. -/
example (setup : ℕ → PMF F.Desc) (h : F.CDH setup) :
    Negligible fun n => Game.succProbability (F.blindedCDHGame setup (copyBlindedAdversary F) n) :=
  h.negligible_blindedCDHGame _ (copyBlindedAdversary_isPPT F)

/-- The two-point blinded CDH adversary that answers exponents `0`, `0` and its input `u` three
times. -/
noncomputable def copyBlindedPairAdversary : F.BlindedCDHPairAdversary :=
  fun _ _ _ _ u => pure ⟨0, 0, u, u, u⟩

/-- `copyBlindedPairAdversary` is uniform strict PPT, so `BlindedCDHPairAdversary.IsPPT` is
satisfiable in every family. -/
theorem copyBlindedPairAdversary_isPPT : (copyBlindedPairAdversary F).IsPPT := by
  have hu := F.encBlindedCDHPairInput_leftPublic_polyTime .id'
  refine (encBlindedCDHPairAnswerWords_mk_polyTime (.const 0) (.const 0) hu hu hu).isPPTOn.congr
    fun x => ?_
  simp [copyBlindedPairAdversary, blindedCDHPairAnswerWords]

/-- The certified reduction of Lemma 21.8 at this adversary. -/
example : (F.blindedCDHPairToCDHAdversary (copyBlindedPairAdversary F)).IsPPT :=
  isPPT_blindedCDHPairToCDHAdversary (copyBlindedPairAdversary_isPPT F)

/-- The sampling loss of Lemma 21.8 at this adversary. -/
example (setup : ℕ → PMF F.Desc) (n : ℕ) :
    Game.succProbability (F.blindedCDHPairGame setup (copyBlindedPairAdversary F) n) ≤
      Game.succProbability
          (F.cdhGame setup (F.blindedCDHPairToCDHAdversary (copyBlindedPairAdversary F)) n) +
        1 / 2 ^ n :=
  F.succProbability_blindedCDHPairGame_le setup _ n

/-- Lemma 21.8 applied as a client would. -/
example (setup : ℕ → PMF F.Desc) (h : F.CDH setup) :
    Negligible fun n =>
      Game.succProbability (F.blindedCDHPairGame setup (copyBlindedPairAdversary F) n) :=
  h.negligible_blindedCDHPairGame _ (copyBlindedPairAdversary_isPPT F)

end Family

/-- Both theorems on Schnorr groups. -/
example (setup : ℕ → PMF schnorrGroups.Desc) (h : schnorrGroups.CDH setup) :
    (Negligible fun n => Game.succProbability
      (schnorrGroups.blindedCDHGame setup (copyBlindedAdversary schnorrGroups) n)) ∧
    Negligible fun n => Game.succProbability
      (schnorrGroups.blindedCDHPairGame setup (copyBlindedPairAdversary schnorrGroups) n) :=
  ⟨h.negligible_blindedCDHGame _ (copyBlindedAdversary_isPPT _),
    h.negligible_blindedCDHPairGame _ (copyBlindedPairAdversary_isPPT _)⟩

end CslibFrontierTests.Crypto.BlindedCDH
