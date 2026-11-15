/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Game.SecondPreimage
public import CslibFrontier.Crypto.Negligible.Basic
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Probability.PMF
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Asymptotic second-preimage resistance on bit strings

A function `f` is second-preimage resistant ([BonehShoup2023], Section 8.11.1, Definition 8.6,
p. 336) when, given a uniformly sampled input `x` and the unary security parameter `n`, every
efficient adversary has negligible probability of finding `x' ≠ x` with `f x' = f x`.

In Boneh–Shoup Definition 8.6 (`m' ∈ M`), the adversary's answer is restricted to the message space.
Here `secondPreimageGame` draws an `n`-bit input `x ← {0,1}ⁿ` and accepts an answer `x'` of any
length, matching the any-length preimage convention of `Cslib.Crypto.OneWay`; this is at least as
strong as Definition 8.6 with `M = {0,1}ⁿ`.

This module defines the uniform bit-string game `secondPreimageGame f adversary n`, its strict
PPT certificates, and `SecondPreimageResistant f` on `List Bool → List Bool`, along with
`SecondPreimageResistant.of_injective` and `not_secondPreimageResistant_const`. The monad-generic
finite experiment and distributional bounds of Exercise 8.23(a)–(b) live in
`CslibFrontier.Crypto.Game.SecondPreimage`; the certified bit-string reductions of (8.17),
Exercise 8.23(b)–(d), and Theorem 8.12 are not proved here.

## Main definitions

* `Cslib.Crypto.SecondPreimageFinder`: `ℕ → List Bool → ProbComp (List Bool)`.
* `Cslib.Crypto.secondPreimageGame`: `secondPreimageExperiment` on uniform `n`-bit inputs.
* `Cslib.Crypto.SecondPreimageResistant`: polynomial-time evaluation and negligible success in
  `secondPreimageGame` for every uniform strict PPT `SecondPreimageFinder`.

## Main results

* `Cslib.Crypto.isPPTOn_secondPreimageGame`, `Cslib.Crypto.isPPT_secondPreimageGame`: the
  second-preimage experiment is uniformly strict PPT.
* `Cslib.Crypto.SecondPreimageResistant.of_injective`: any injective polynomial-time function is
  unconditionally second-preimage resistant.
* `Cslib.Crypto.not_secondPreimageResistant_of_le_succProbability`,
  `Cslib.Crypto.not_secondPreimageResistant_const`: finding second preimages with probability
  bounded away from zero refutes `SecondPreimageResistant`; constant functions are not
  second-preimage resistant.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1, Definition 8.6, p. 336.
-/

public section

namespace Cslib.Crypto

open ProbComp Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- A second-preimage finder receives the unary parameter and the sampled input word. -/
abbrev SecondPreimageFinder := ℕ → List Bool → ProbComp (List Bool)

/-- The second-preimage game at length `n` ([BonehShoup2023], Section 8.11.1, Definition 8.6,
p. 336): `secondPreimageExperiment` for `f` on a uniform `n`-bit input, with the finder told `n`.
Unlike the source's `m' ∈ M`, any word `x' ≠ x` with `f x' = f x` wins. -/
@[expose]
noncomputable def secondPreimageGame (f : List Bool → List Bool)
    (adversary : SecondPreimageFinder) (n : ℕ) : ProbComp Bool :=
  secondPreimageExperiment (BitString.sampleList n) f (adversary n)

/-- Run the complete second-preimage experiment on its unary parameter. -/
@[program_certificate]
theorem isPPTOn_secondPreimageGame {f : List Bool → List Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPTOn encUnary encBool (secondPreimageGame f adversary) := by
  unfold secondPreimageGame secondPreimageExperiment
  ppt

/-- The second-preimage experiment is uniformly PPT, independently of the unused auxiliary input. -/
@[program_certificate]
theorem isPPT_secondPreimageGame {f : List Bool → List Bool} {adversary : SecondPreimageFinder}
    (hf : ComputableInPolyTime f encBits encBits) (ha : IsPPT encBits adversary) :
    IsPPT encBool (fun n _ => secondPreimageGame f adversary n) := by ppt

/-- One plain polynomial-time algorithm evaluates the function, and every uniform strict PPT
second-preimage finder has negligible success over the uniform `n`-bit input and its own
independent random coins ([BonehShoup2023], Section 8.11.1, Definition 8.6, p. 336).

Deviation from the source: Definition 8.6 restricts the adversary's answer to the message space,
`m' ∈ M`, whereas `secondPreimageGame` accepts an answer of any length (matching
`Cslib.Crypto.OneWay`), which is at least as strong as Definition 8.6 with `M = {0,1}ⁿ`. -/
structure SecondPreimageResistant (f : List Bool → List Bool) : Prop where
  /-- A deterministic polynomial-time algorithm evaluates the function. -/
  polyTime : ComputableInPolyTime f encBits encBits
  /-- Second-preimage search is indistinguishable from certain failure in the common game
  calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (secondPreimageGame f adversary n))
    (fun _ _ => PMF.pure false) (IsPPT encBits)

/-- The shared game definition gives negligible second-preimage success probability. -/
theorem SecondPreimageResistant.negligible {f : List Bool → List Bool}
    (h : SecondPreimageResistant f) (adversary : SecondPreimageFinder)
    (hPPT : IsPPT encBits adversary) :
    Negligible
      (fun n => Game.succProbability (ProbComp.eval (secondPreimageGame f adversary n))) := by
  simpa only [Game.advantage_pure_false] using h.secure adversary hPPT

/-- Establish second-preimage resistance by bounding every efficient finder's success
probability. -/
theorem SecondPreimageResistant.of_negligible {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits)
    (h : ∀ adversary : SecondPreimageFinder, IsPPT encBits adversary →
      Negligible
        (fun n => Game.succProbability (ProbComp.eval (secondPreimageGame f adversary n)))) :
    SecondPreimageResistant f := by
  refine ⟨hf, fun adversary hPPT => ?_⟩
  simpa only [Game.advantage_pure_false] using h adversary hPPT

/-- Any injective polynomial-time function is unconditionally second-preimage resistant. -/
theorem SecondPreimageResistant.of_injective {f : List Bool → List Bool}
    (hf : ComputableInPolyTime f encBits encBits) (hinj : Function.Injective f) :
    SecondPreimageResistant f := by
  refine ⟨hf, fun adversary _ => ?_⟩
  simp only [secondPreimageGame, eval_secondPreimageExperiment,
    secondPreimageExperiment_eq_pure_false_of_injective _ hinj, Game.advantage_self,
    negligible_zero]

/-- **Finding second preimages with probability bounded away from zero refutes
`SecondPreimageResistant`**: an efficient finder whose success probability is at least a fixed
`c > 0` at every length. -/
theorem not_secondPreimageResistant_of_le_succProbability {f : List Bool → List Bool} {c : ℝ≥0}
    (hc : c ≠ 0) (finder : SecondPreimageFinder) (hPPT : IsPPT encBits finder)
    (h : ∀ n, c ≤ Game.succProbability (ProbComp.eval (secondPreimageGame f finder n))) :
    ¬ SecondPreimageResistant f := fun hf =>
  not_negligible_const hc (negligible_of_le (hf.negligible finder hPPT) h)

/-- Constant functions are not second-preimage resistant: prepending `true` always gives a
distinct word with the same constant image. -/
theorem not_secondPreimageResistant_const (word : List Bool) :
    ¬ SecondPreimageResistant (fun _ => word) := by
  refine not_secondPreimageResistant_of_le_succProbability one_ne_zero
    (fun _ x => pure (true :: x)) ?_ fun n => ?_
  · have h : ComputableInPolyTime (List.cons true) encBits encBits := by polytime
    exact h.isPPT
  · have hcond (x : List Bool) : ((true :: x != x) && (word == word)) = true := by
      rw [Bool.and_eq_true, bne_iff_ne, beq_self_eq_true]
      exact ⟨ne_of_apply_ne List.length (by simp), rfl⟩
    have heval :
        ProbComp.eval (secondPreimageGame (fun _ => word) (fun _ x => pure (true :: x)) n) =
          PMF.pure true := by
      simp only [secondPreimageGame, secondPreimageExperiment, ProbComp.eval_bind,
        ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, hcond, PMF.bind_const]
    rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

end Cslib.Crypto
