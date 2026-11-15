/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.CompositeResiduosity
import CslibFrontier.Crypto.Computational.RabinFactoring
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for Rabin squaring and factoring equivalence
-/

namespace CslibFrontierTests.Crypto.RabinFactoring

open Cslib Cslib.Crypto

/-- Smallest Blum integer `N = 3 * 7 = 21` (`3 ≡ 3 [MOD 4]`, `7 ≡ 3 [MOD 4]`). -/
def blum21 : BlumDesc :=
  ⟨(3, 7), ⟨⟨by norm_num, by decide⟩, ⟨by norm_num, by decide⟩, by decide⟩⟩

example : blum21.modulus = 21 := rfl

example : rabinEval 21 2 = 4 := by decide

example : rabinEval 21 5 = 4 := by decide

example : rabinFactorPair (2 + 5) 21 = (7, 3) := by decide

example : crtSqrt (rabinEval 21 5) 3 7 ^ 2 % 21 = rabinEval 21 5 := by decide

noncomputable example (gen : BlumGen) (F : ℕ → ℕ → _) (n : ℕ) :
    Game.succProbability (factoringGame gen F n) ≤
      Game.succProbability (rabinInversionGame gen (factorToRabin F) n) :=
  succProbability_factoringGame_le gen F n

example (gen : BlumGen) (h : FactoringHard gen) : RabinOneWay gen :=
  (rabinOneWay_iff_factoringHard gen).mpr h

/-- info: 'Cslib.Crypto.factoringHard_of_rabinOneWay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.factoringHard_of_rabinOneWay

/-- info: 'Cslib.Crypto.rabinOneWay_of_factoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.rabinOneWay_of_factoringHard

/-! ### Quadratic residuosity and decisional composite residuosity imply integer factoring -/

/-- `4 = 2 ^ 2` is a quadratic residue modulo `21 = 3 * 7`, so `qrEulerTest 21 4 3 7 = true`. -/
example : qrEulerTest 21 4 3 7 = true := by decide

/-- `20 ≡ -1 [MOD 21]` is a positive-Jacobi quadratic nonresidue modulo `21 = 3 * 7`, so
`qrEulerTest 21 20 3 7 = false`. -/
example : qrEulerTest 21 20 3 7 = false := by decide

/-- `2 ^ 15 % 225 = 143` is a `15`-th residue modulo `15 ^ 2 = 225` (`143 ^ 8 % 225 = 1`), whereas
`16 = 1 + 15` has order `15` (`16 ^ 8 % 225 = 121 ≠ 1`). -/
example : dcrTotientTest 15 (2 ^ 15 % 225) 3 5 = true := by decide

example : dcrTotientTest 15 16 3 5 = false := by decide

example (setup : ℕ → PMF ModulusDesc) (h : QuadraticResiduosityHard setup) :
    ModulusFactoringHard (fun n => (setup n).map ModulusDesc.modulus) :=
  h.modulusFactoringHard

example (gen : BlumGen) (setup : ℕ → PMF ModulusDesc)
    (h : QuadraticResiduosityHard setup)
    (hmod : ∀ n, (setup n).map ModulusDesc.modulus = (gen n).map BlumDesc.modulus) :
    FactoringHard gen :=
  h.factoringHard hmod

example (setup : ℕ → PMF BalancedModulus.Desc) (h : DCR setup) :
    ModulusFactoringHard (fun n => (setup n).map BalancedModulus.Desc.modulus) :=
  h.modulusFactoringHard

example (gen : BlumGen) (setup : ℕ → PMF BalancedModulus.Desc)
    (h : DCR setup)
    (hmod : ∀ n, (setup n).map BalancedModulus.Desc.modulus = (gen n).map BlumDesc.modulus) :
    FactoringHard gen :=
  FactoringHard.of_modulusFactoringHard h.modulusFactoringHard hmod

/-- info: 'Cslib.Crypto.QuadraticResiduosityHard.modulusFactoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.QuadraticResiduosityHard.modulusFactoringHard

/-- info: 'Cslib.Crypto.QuadraticResiduosityHard.factoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.QuadraticResiduosityHard.factoringHard

/-- info: 'Cslib.Crypto.DCR.modulusFactoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.DCR.modulusFactoringHard

/-- info: 'Cslib.Crypto.FactoringHard.of_modulusFactoringHard' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.FactoringHard.of_modulusFactoringHard

end CslibFrontierTests.Crypto.RabinFactoring
