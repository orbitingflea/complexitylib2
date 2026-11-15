/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.SIS.MLKEM.Asymptotic
import CslibFrontier.Probability.PMF

/-!
# The hypotheses of K-PKE IND-CPA with ideal coin expansion hold together

`indCPA_kpkeIdealCoins_of_decisionModuleLWEWith` assumes a parameter family computable in
polynomial time and two instances of `DecisionModuleLWEWith`. At modulus `1` there is only one
Module-LWE sample, so both instances hold for every shape and every pair of laws
(`decisionModuleLWEWith_one`). The constant family `trivialParams` therefore satisfies every
hypothesis at once, and the theorem applies to it. This checks that the hypotheses are jointly
satisfiable; it says nothing about hardness at meaningful parameters, where
`DecisionModuleLWEWith` is an assumption.
-/

public section

namespace CslibFrontierTests.Crypto.MLKEMAsymptotic

open Cslib Cslib.Crypto Cslib.Crypto.MLKEM Turing.MultiTapeTM Probability

/-- The constant parameter set with modulus `1`. -/
def trivialParams : Params := { n := 1, q := 1, k := 1, η₁ := 1, η₂ := 1, du := 1, dv := 1 }

instance : NeZero trivialParams.q := ⟨one_ne_zero⟩

/-- At modulus `1`, decision Module-LWE holds for every shape and pair of laws: the real and random
games coincide, since every vector over `ZMod 1` is zero. -/
theorem decisionModuleLWEWith_one (m d n : ℕ → ℕ)
    (secret : (κ : ℕ) → PMF (Fin (d κ) → Fin (n κ) → ZMod 1))
    (error : (κ : ℕ) → PMF (Fin (m κ) → Fin (n κ) → ZMod 1)) :
    DecisionModuleLWEWith m d n (fun _ => 1) secret error := by
  intro D _
  refine negligible_of_le negligible_zero fun κ => le_of_eq ?_
  have hgame : ModuleLWE.realGame (secret κ) (error κ) (D κ) = ModuleLWE.randomGame (D κ) := by
    rw [ModuleLWE.realGame_eq_uniform_bind, ModuleLWE.randomGame, ModuleLWE.eval_randomExperiment]
    refine congrArg _ (funext fun A => ?_)
    simp only [Subsingleton.elim _ (0 : Fin (m κ) → Fin (n κ) → ZMod 1), PMF.bind_const]
  dsimp only
  rw [hgame, Game.advantage_self]

/-- The theorem applies to the constant family with modulus `1`. -/
example : (kpke fun _ => trivialParams).INDCPA :=
  indCPA_kpkeIdealCoins_of_decisionModuleLWEWith (ComputableInPolyTime.const trivialParams)
    (decisionModuleLWEWith_one _ _ _ _ _) (decisionModuleLWEWith_one _ _ _ _ _)

end CslibFrontierTests.Crypto.MLKEMAsymptotic
