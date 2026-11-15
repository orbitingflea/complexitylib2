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
public import CslibFrontier.Probability.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.UniformIndex
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
reduction draws its position with `Cslib.ProbComp.sampleDyadicIndex`, exactly uniform below the
power of two `dyadicSize (Q n)`, which lies in `(Q n, 2 * (Q n + 1)]`. A position at or beyond
`Q n` returns an entry that does not count or the generator. The loss factor is therefore
`dyadicSize (Q n)`, at most `2 * (Q n + 1)`, instead of the book's `Q`; it is still polynomial.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ListCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ListCDHAdversary.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.listCDHGame`: the list form of CDH over the family.
* `Cslib.Crypto.PrimeOrderGroupFamily.listCDHToCDHAdversary`: the guessing reduction as a CDH
  adversary.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_listCDHToCDHAdversary`: the reduction is PPT when the
  list adversary is and `Q` is computable in polynomial time in unary.
* `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_listCDHGame_le`: the loss factor
  `dyadicSize (Q n)`.
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
the list adversary, draw a position with `Cslib.ProbComp.sampleDyadicIndex (Q n)` and return the
entry there, or the generator past the end of the list (`Cslib.Crypto.listCDHToCDH`). -/
noncomputable def listCDHToCDHAdversary (Q : ℕ → ℕ) (adversary : F.ListCDHAdversary) :
    F.CDHAdversary :=
  fun n d => listCDHToCDH (F.generator d) (ProbComp.sampleDyadicIndex (Q n)) (adversary n d)

/-- The word of an entry read with a fallback, as the machine reads it from the framed list of
words. -/
private theorem encode_getD (d : F.Desc) (l : List (F.Carrier d)) (i : ℕ) (x : F.Carrier d) :
    F.encode d (l.getD i x) = ((l.map (F.encode d))[i]?).getD (F.encode d x) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, Option.getD_map]

variable {F} in
/-- **The guessing reduction is efficient**: it is uniform strict PPT whenever the list adversary
is and the bound `Q` is computable in polynomial time in unary. -/
theorem isPPT_listCDHToCDHAdversary {Q : ℕ → ℕ} (hQ : ComputableInPolyTime Q encUnary encUnary)
    {adversary : F.ListCDHAdversary} (hA : adversary.IsPPT) :
    (F.listCDHToCDHAdversary Q adversary).IsPPT := by
  -- the position, drawn from the CDH input and the adversary's words
  let E := encPair F.encCDHInput (encList encBits)
  have hx : ComputableInPolyTime (fun p : F.CDHInput × List (List Bool) => p.1) E
      F.encCDHInput := by
    fun_prop
  have hsample : IsPPTOn E encUnary
      (fun p : F.CDHInput × List (List Bool) => ProbComp.sampleDyadicIndex (Q p.1.secParam)) :=
    isPPTOn_sampleDyadicIndex (hQ.comp (F.encCDHInput_secParam_polyTime hx))
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
        ProbComp.sampleDyadicIndex (Q x.secParam)) :=
    hA.bind_with (hsample.map_with hout)
  refine hprog.congr fun x => ?_
  simp only [listCDHToCDHAdversary, listCDHToCDH, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.map_bind, PMF.bind_map, PMF.pure_map, Function.comp_def,
    encode_getD]
  rfl

/-- **Loss of the guessing reduction**: the list form of CDH with bound `Q` is won with probability
at most `dyadicSize (Q n)` times the success probability of the reduction in the CDH game. The
factor is the size of the power-of-two range of the position, at most `2 * (Q n + 1)`
(`Cslib.Probability.dyadicSize_le`). It holds for every `Q`, every setup law and every
adversary. -/
theorem succProbability_listCDHGame_le (setup : ℕ → PMF F.Desc) (Q : ℕ → ℕ)
    (adversary : F.ListCDHAdversary) (n : ℕ) :
    Game.succProbability (F.listCDHGame setup Q adversary n) ≤
      dyadicSize (Q n) *
        Game.succProbability (F.cdhGame setup (F.listCDHToCDHAdversary Q adversary) n) := by
  have hle : F.listCDHGame setup Q adversary n true ≤
      (dyadicSize (Q n) : ℝ≥0∞) *
        F.cdhGame setup (F.listCDHToCDHAdversary Q adversary) n true := by
    refine PMF.bind_apply_le_mul_bind_apply _ fun d => ?_
    refine eval_listCDHExperiment_le_mul (F.order d) (F.generator d) (Q n)
      (ProbComp.sampleDyadicIndex (Q n)) (fun l x hx => ?_) (adversary n d)
    rw [ProbComp.eval_sampleDyadicIndex, PMF.map_comp]
    have hx' : x ∈ l.take (dyadicSize (Q n)) :=
      List.take_subset_take_left l (lt_dyadicSize (Q n)).le hx
    calc (1 : ℝ≥0∞) = (dyadicSize (Q n) : ℝ≥0∞) * (dyadicSize (Q n) : ℝ≥0∞)⁻¹ :=
          (ENNReal.mul_inv_cancel (by simp [(dyadicSize_pos _).ne'])
            (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := mul_le_mul' le_rfl (PMF.inv_le_map_uniformOfFintype_getD (F.generator d) hx')
  simp only [Game.succProbability]
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_mul]
  exact ENNReal.toNNReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _))
    hle

/-- **The list form of CDH is hard under CDH** ([BonehShoup2023], Section 21.11.4, p. 908): under
the CDH assumption, every PPT list adversary wins the list form of CDH with negligible probability,
for every bound `Q` computable in polynomial time in unary. -/
theorem CDH.negligible_listCDHGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.CDH setup) {Q : ℕ → ℕ} (hQ : ComputableInPolyTime Q encUnary encUnary)
    (adversary : F.ListCDHAdversary) (hA : adversary.IsPPT) :
    Negligible fun n => Game.succProbability (F.listCDHGame setup Q adversary n) := by
  have hcdh := h _ (isPPT_listCDHToCDHAdversary hQ hA)
  negligible using F.succProbability_listCDHGame_le setup Q adversary

end Cslib.Crypto.PrimeOrderGroupFamily
