/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.Encryption.Basic
import CslibFrontier.Crypto.Computational.Encryption.Deterministic
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Tests and hypothesis probes for deterministic public-key encryption

An ordinary `module` client of `CslibFrontier.Crypto.Computational.Encryption.Deterministic`
([BonehShoup2023], Section 11.3.1, pp. 438–439):

* Sending the plaintext bit under the empty key pair fails `Encryption.INDCPA` by
  `Encryption.not_indcpaOn_of_deterministic`.
* **Probe 1 (`hcorrect`):** `constCipher`, which maps every message to `[]`, is deterministic and
  admits two distinct messages, yet is `Encryption.INDCPA` with advantage `0` against every
  adversary because it is not correct.
* **Probe 2 (`hvalid`):** under the never-admissible predicate `fun _ _ _ _ => false`, the
  plaintext cipher satisfies `Encryption.INDCPAOn`.
* **Probe 3 (`hm`):** on the one-element message space `Unit`, the correct deterministic
  `unitCipher` satisfies `Encryption.INDCPAOf`.
* **Probe 4 (`hdet`):** at a fixed parameter, `coinCipher`, which appends a fresh uniform bit to
  the message bit, is `PKE.Correct`, but `true` lies in the support of
  `coinCipher.cpaExperiment (fun _ _ _ => true) (coinCipher.detAdversary false true) false`, so
  `PKE.eval_cpaExperiment_detAdversary_false` fails without determinism.
-/

public section

namespace CslibFrontierTests.Crypto.DeterministicPKE

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Encryption Turing.MultiTapeTM

/-- The empty key pair (as in `CslibFrontierTests.Crypto.AssumptionNonvacuity`). -/
noncomputable def emptyKeys : ℕ → ProbComp (List Bool × List Bool) := fun _ => pure ([], [])

/-- Send the plaintext bit as the one-bit ciphertext. -/
noncomputable def plaintext : ℕ → List Bool → Bool → ProbComp (List Bool) := fun _ _ b => pure [b]

-- Sending the plaintext bit is not IND-CPA, as an instance of `not_indcpaOn_of_deterministic`.
example : ¬ Encryption.INDCPA emptyKeys plaintext :=
  not_indcpaOn_of_deterministic (fun _ _ c => c.head?) (m₀ := fun _ => false)
    (m₁ := fun _ => true) 0
    (by unfold plaintext; ppt) (by fun_prop) (by fun_prop)
    (fun n _ keys _ m c hc => by
      simp only [plaintext, ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hc
      simp [hc])
    (by simp) (by simp) (fun n _ keys _ => ⟨[false], by simp [plaintext]⟩)

-- `Encryption.detAdversary` against `plaintext` with messages `false` and `true` is uniform strict
-- PPT and achieves `game` advantage `1` at every security parameter.
example : (Encryption.detAdversary plaintext (fun _ => false) (fun _ => true)).IsPPT encBool :=
  isPPT_detAdversary (by unfold plaintext; ppt) (by fun_prop) (by fun_prop)

example (n : ℕ) :
    Encryption.advantage (Encryption.game emptyKeys plaintext
      (Encryption.detAdversary plaintext (fun _ => false) (fun _ => true))) n = 1 :=
  advantage_gameOn_detAdversary (fun _ _ _ _ => true) emptyKeys plaintext (fun _ => false)
    (fun _ => true) n (by simp) (fun _ _ => ⟨[false], by simp [plaintext]⟩)
    (fun _ _ c₁ hc₁ hc₀ => by simp_all [plaintext])

/-- Probe 1 (`hcorrect`): the constant ciphertext `[]` is deterministic with two distinct admissible
messages and satisfies `INDCPA`. -/
noncomputable def constCipher : ℕ → List Bool → Bool → ProbComp (List Bool) := fun _ _ _ => pure []

example : Encryption.INDCPA emptyKeys constCipher := fun A _ =>
  negligible_zero.congr fun n => by
    simp [Encryption.gameOn, constCipher, Game.advantage]

-- Probe 2 (`hvalid`): with no admissible message pair, the plaintext cipher satisfies `INDCPAOn`.
example : Encryption.INDCPAOn (fun _ _ _ _ => false) encBool emptyKeys plaintext := fun A _ =>
  negligible_zero.congr fun n => by
    simp [Encryption.gameOn, Game.advantage]

/-- Probe 3 (`hm`): on a one-message space, the deterministic, correct cipher is secure. -/
noncomputable def unitCipher : ℕ → List Bool → Unit → ProbComp (List Bool) := fun _ _ _ => pure []

example : (PKE.mk (emptyKeys 0) (unitCipher 0) (fun _ _ => some ())).Correct :=
  fun _ _ _ _ _ => rfl

example (encU : Unit ↪ List Bool) : Encryption.INDCPAOf encU emptyKeys unitCipher := fun A _ =>
  negligible_zero.congr fun n => by
    simp [Encryption.gameOn, unitCipher, Game.advantage]

/-- Probe 4 (`hdet`), at a fixed parameter: with a fresh uniform bit appended, the scheme is
correct, but the adversary's experiment `false` is not the point mass at `false`. -/
noncomputable def coinCipher : PKE Unit Unit Bool (Bool × Bool) where
  keyGen := pure ((), ())
  encrypt _ m := do
    let r ← ProbComp.uniform Bool
    return (m, r)
  decrypt _ c := some c.1

example : coinCipher.Correct := by
  intro keys _ m c hc
  simp only [coinCipher, ProbComp.eval_bind, ProbComp.eval_pure, PMF.support_bind,
    PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at hc
  obtain ⟨r, -, rfl⟩ := hc
  rfl

example : true ∈ (ProbComp.eval (coinCipher.cpaExperiment (fun _ _ _ => true)
    (coinCipher.detAdversary false true) false)).support := by
  simp only [PKE.cpaExperiment, lrExperiment, PKE.detAdversary, coinCipher, ProbComp.eval_bind,
    ProbComp.eval_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
  simp

end CslibFrontierTests.Crypto.DeterministicPKE
