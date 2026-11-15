/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiffieHellman.ListCDH
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Tactic.Negligible

/-!
# The list form of the Computational Diffie–Hellman problem over a group family

Over a `PrimeOrderGroupFamily`, this module states the list form of CDH as a game, with a
polynomial bound `Q` on the number of entries that count. It gives the guessing reduction of
[BonehShoup2023], Section 21.11.4 (p. 908) and the proof of Theorem 11.4 (pp. 446–448), which turns
a list adversary into a CDH adversary, with a PPT certificate, and proves that under the CDH
assumption every PPT list adversary wins with negligible probability. The fixed-group experiment,
the reduction for a given index sampler and its analysis are in
`CslibFrontier/Crypto/Computational/DiffieHellman/ListCDH.lean`, whose module docstring lists the
differences from the book and the behaviour at `Q = 0`, for short lists and for repeated entries.

A list adversary's efficiency is stated on encodings, as for `CDHAdversary.IsPPT`: one uniform
strict PPT machine reads `encCDHInput` and writes the framed list of the words of its entries.

A machine with fair coins cannot draw an exactly uniform position below every `Q n`, so the
reduction draws its position with `Cslib.ProbComp.sampleModIndex (width n) (Q n)`: the residue
modulo `Q n` of a number written with `width n` fair coins, capped at `Q n` (which matters only at
`Q n = 0`). The coin count `width` is a parameter of the reduction. Each position below `Q n` is
drawn with probability at least `1 / Q n - 1 / 2 ^ width n`, so the reduction keeps the book's
factor `Q n` and adds the term `Q n / 2 ^ width n`. With `width n = n` that term is negligible when
`Q` is polynomially bounded, which gives the conclusion under the CDH assumption.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ListCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ListCDHAdversary.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.listCDHGame`: the list form of CDH over the family.
* `Cslib.Crypto.PrimeOrderGroupFamily.listCDHToCDHAdversary`: the guessing reduction as a CDH
  adversary.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_listCDHToCDHAdversary`: the reduction is PPT when the
  list adversary is and `width` and `Q` are computable in polynomial time in unary.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_listCDHGame_le`: the loss, the factor `Q n`
  plus the term `Q n / 2 ^ width n`, for every `width` and `Q`.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_listCDHGame_mono`: the success probability
  does not decrease when the bound `Q n` grows.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_listCDHGame`: under the CDH assumption every
  PPT list adversary wins with negligible probability.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 21.11.4, p. 908, and Section 11.5.1, Theorem 11.4 and its
  proof with equation (11.12), pp. 446–448.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-- A list adversary for CDH over the family: given the security parameter, the group parameters
and two elements, it returns a list of elements of the group. -/
abbrev ListCDHAdversary : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → ProbComp (List (F.Carrier d))

variable {F} in
/-- A list adversary is PPT when one uniform strict PPT machine reads `encCDHInput` and writes the
framed list of the words of the adversary's entries. -/
@[expose] def ListCDHAdversary.IsPPT (adversary : F.ListCDHAdversary) : Prop :=
  IsPPTOn F.encCDHInput (encList encBits) fun x =>
    List.map (F.encode x.groupParameters) <$>
      adversary x.secParam x.groupParameters x.leftPublic x.rightPublic

/-- The list form of CDH with bound `Q`: choose group parameters with the setup law, then run
`Cslib.Crypto.listCDHExperiment` with bound `Q n` in that group. -/
@[expose] noncomputable def listCDHGame (setup : ℕ → PMF F.Desc) (Q : ℕ → ℕ)
    (adversary : F.ListCDHAdversary) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    listCDHExperiment (F.order d) (F.generator d) (Q n) (adversary n d)

/-- The guessing reduction of [BonehShoup2023], Section 21.11.4 (p. 908), as a CDH adversary: run
the list adversary, draw a position with `Cslib.ProbComp.sampleModIndex (width n) (Q n)` from
`width n` fair coins, and return the entry there, or the generator past the end of the list
(`Cslib.Crypto.listCDHToCDH`). -/
noncomputable def listCDHToCDHAdversary (width Q : ℕ → ℕ) (adversary : F.ListCDHAdversary) :
    F.CDHAdversary :=
  fun n d => listCDHToCDH (F.generator d) (ProbComp.sampleModIndex (width n) (Q n)) (adversary n d)

/-- The word of an entry read with a fallback, as the machine reads it from the framed list of
words. -/
private theorem encode_getD (d : F.Desc) (l : List (F.Carrier d)) (i : ℕ) (x : F.Carrier d) :
    F.encode d (l.getD i x) = ((l.map (F.encode d))[i]?).getD (F.encode d x) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

variable {F} in
/-- **The guessing reduction is efficient**: it is uniform strict PPT whenever the list adversary
is and the coin count `width` and the bound `Q` are computable in polynomial time in unary. -/
theorem isPPT_listCDHToCDHAdversary {width Q : ℕ → ℕ}
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : F.ListCDHAdversary} (hA : adversary.IsPPT) :
    (F.listCDHToCDHAdversary width Q adversary).IsPPT := by
  -- the position, drawn from the CDH input and the adversary's words
  let E := encPair F.encCDHInput (encList encBits)
  have hx : ComputableInPolyTime (fun p : F.CDHInput × List (List Bool) => p.1) E
      F.encCDHInput := by
    fun_prop
  have hn := F.encCDHInput_secParam_polyTime hx
  have hsample : IsPPTOn E encUnary (fun p : F.CDHInput × List (List Bool) =>
      ProbComp.sampleModIndex (width p.1.secParam) (Q p.1.secParam)) :=
    isPPTOn_sampleModIndex (hwidth.comp hn) (hQ.comp hn)
  -- the output, read from the words at the position with the generator's word as fallback
  let E' := encPair E encUnary
  have hx' : ComputableInPolyTime
      (fun p : (F.CDHInput × List (List Bool)) × ℕ => p.1.1) E' F.encCDHInput := by fun_prop
  have hd' := F.encCDHInput_groupParameters_polyTime hx'
  have hwords : ComputableInPolyTime
      (fun p : (F.CDHInput × List (List Bool)) × ℕ => p.1.2) E' (encList encBits) := by fun_prop
  have hi : ComputableInPolyTime
      (fun p : (F.CDHInput × List (List Bool)) × ℕ => p.2) E' encUnary := by fun_prop
  have hout : ComputableInPolyTime
      (fun p : (F.CDHInput × List (List Bool)) × ℕ => (p.1.2[p.2]?).getD
        (F.encode p.1.1.groupParameters (F.generator p.1.1.groupParameters))) E' encBits :=
    ComputableInPolyTime.optionGetDWithInput (ComputableInPolyTime.getElem? hwords hi)
      (computableInPolyTime_encode_generator hd')
  have hprog : IsPPTOn F.encCDHInput encBits (fun x : F.CDHInput => do
      let words ← List.map (F.encode x.groupParameters) <$>
        adversary x.secParam x.groupParameters x.leftPublic x.rightPublic
      (fun i => (words[i]?).getD (F.encode x.groupParameters (F.generator x.groupParameters))) <$>
        ProbComp.sampleModIndex (width x.secParam) (Q x.secParam)) :=
    hA.bind_with (hsample.map_with hout)
  refine hprog.congr fun x => ?_
  simp only [listCDHToCDHAdversary, listCDHToCDH, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def,
    encode_getD]
  rfl

/-- **Loss of the guessing reduction**: the list form of CDH with bound `Q` is won with probability
at most `Q n` times the success probability of the reduction in the CDH game, plus
`Q n / 2 ^ width n`. The factor is the book's `Q` ([BonehShoup2023], Section 21.11.4, p. 908,
and equation (11.12), p. 448); the additive term, which the book does not have, is the cost of
drawing the position from `width n` fair coins. It holds for every setup law, every `width`, every
`Q`, including `Q n = 0`, and every adversary. -/
theorem succProbability_listCDHGame_le (setup : ℕ → PMF F.Desc) (width Q : ℕ → ℕ)
    (adversary : F.ListCDHAdversary) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup Q adversary n) ≤
      Q n * Game.succProbability
          (F.cdhGame setup (F.listCDHToCDHAdversary width Q adversary) n) +
        Q n / 2 ^ width n := by
  have hle : F.listCDHGame setup Q adversary n true ≤
      (Q n : ℝ≥0∞) * F.cdhGame setup (F.listCDHToCDHAdversary width Q adversary) n true +
        (Q n : ℝ≥0∞) / 2 ^ width n :=
    PMF.bind_apply_le_mul_bind_apply_add _ fun d =>
      eval_listCDHExperiment_le_mul_add (F.order d) (F.generator d) (width n) (Q n) (adversary n d)
  simp only [Game.succProbability]
  rw [← ENNReal.coe_le_coe]
  push_cast [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_div (pow_ne_zero _ two_ne_zero)]
  exact hle

/-- **More entries that count cannot hurt the adversary**: if `Q n ≤ Q' n`, the list form of CDH
with bound `Q'` is won at `n` with probability at least that with bound `Q`, since the first `Q n`
entries of a list are among its first `Q' n` (`Cslib.Crypto.eval_listCDHExperiment_mono` in each
group). -/
theorem succProbability_listCDHGame_mono (setup : ℕ → PMF F.Desc) {Q Q' : ℕ → ℕ} {n : ℕ}
    (hle : Q n ≤ Q' n) (adversary : F.ListCDHAdversary) :
    Game.succProbability (F.listCDHGame setup Q adversary n) ≤
      Game.succProbability (F.listCDHGame setup Q' adversary n) :=
  Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ =>
    eval_listCDHExperiment_mono (F.order d) (F.generator d) hle (adversary n d))

/-- **The list form of CDH is hard under CDH** ([BonehShoup2023], Section 21.11.4, p. 908): under
the CDH assumption, every PPT list adversary wins the list form of CDH with negligible probability,
for every bound `Q` computable in polynomial time in unary. -/
theorem CDH.negligible_listCDHGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.CDH setup) {Q : ℕ → ℕ} (hQ : ComputableInPolyTime Q encUnary encUnary)
    (adversary : F.ListCDHAdversary) (hA : adversary.IsPPT) :
    Negligible fun n => Game.succProbability (F.listCDHGame setup Q adversary n) := by
  have hcdh := h _ (isPPT_listCDHToCDHAdversary (width := fun n => n) .id' hQ hA)
  negligible using F.succProbability_listCDHGame_le setup (fun n => n) Q adversary

end Cslib.Crypto.PrimeOrderGroupFamily
