/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiffieHellman.Blinded
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Computational.DiscreteLog.Extract
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import Mathlib.Tactic.Module

/-!
# The blinded Diffie–Hellman problems over a group family

Over a `PrimeOrderGroupFamily`, this module states the two problems of [BonehShoup2023],
Section 21.11.5, Lemmas 21.7 and 21.8 (pp. 910–911), as games. It gives the book's reductions,
which turn an adversary for each problem into a CDH adversary, with PPT certificates, and proves
that under the CDH assumption every PPT adversary wins either game with negligible probability.
The fixed-group problems (`Cslib.Crypto.blindedCDHExperiment`,
`Cslib.Crypto.blindedCDHPairExperiment`), the reductions with fixed blinding exponents and their
exact analysis are in `CslibFrontier/Crypto/Computational/DiffieHellman/Blinded.lean`, whose module
docstring lists the differences from the book in one group. The book names neither problem:
"blinded CDH" and "two-point blinded CDH", and the names of all declarations here, are this
library's names.

Adversaries receive and return group elements and exponents. Their efficiency is stated on
encodings, as for `CDHAdversary.IsPPT`: one uniform strict PPT machine reads the encoded input
(`encBlindedCDHInput`, `encBlindedCDHPairInput`) and writes the answer, the exponents as binary
numbers below the group order and the elements as their words.

The reductions draw their blinding exponents with `sampleExp`, the fair-coin sampler of the other
Diffie–Hellman reductions, whose law is within `1 / 2 ^ n` of uniform. The bounds therefore carry a
sampling loss of `2 / 2 ^ n` for Lemma 21.7 (two draws) and `1 / 2 ^ n` for Lemma 21.8 (one draw),
which the book's "we can easily solve" leaves implicit. The theorems assume only `F.CDH setup` and
the adversary's PPT predicate.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encBlindedCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHAdversary.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.blindedCDHGame`: the problem of Lemma 21.7 over the family.
* `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHPairInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encBlindedCDHPairInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHPairAnswerWords`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encBlindedCDHPairAnswerWords`,
  `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHPairAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.BlindedCDHPairAdversary.IsPPT`,
  `Cslib.Crypto.PrimeOrderGroupFamily.blindedCDHPairGame`: the problem of Lemma 21.8 over the
  family.
* `Cslib.Crypto.PrimeOrderGroupFamily.blindedCDHToCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.blindedCDHPairToCDHAdversary`: the book's reductions as CDH
  adversaries.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_blindedCDHToCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_blindedCDHPairToCDHAdversary`: the reductions are PPT
  when the adversaries are. The second follows from
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPTOn_blindedCDHPairToCDHWith`, the same for
  `Cslib.Crypto.blindedCDHPairToCDHWith` with its blinding exponent read from the input.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_blindedCDHGame_cdhGame_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.succProbability_blindedCDHPairGame_le`: the sampling losses
  `2 / 2 ^ n` and `1 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_blindedCDHGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CDH.negligible_blindedCDHPairGame`: Lemmas 21.7 and 21.8
  under the CDH assumption.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 21.11.5, Lemmas 21.7 and 21.8, pp. 910–911.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### Lemma 21.7 -/

/-- The input of an adversary in the blinded CDH game: the security parameter, public group
parameters and the four elements `a`, `b`, `u`, `v` of [BonehShoup2023], Lemma 21.7. -/
structure BlindedCDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group. -/
  groupParameters : F.Desc
  /-- The first blinding element, `a = α • g` in the experiment. -/
  leftBlind : F.Carrier groupParameters
  /-- The second blinding element, `b = β • g` in the experiment. -/
  rightBlind : F.Carrier groupParameters
  /-- The first public element, `u = x • g` in the experiment. -/
  leftPublic : F.Carrier groupParameters
  /-- The second public element, `v = y • g` in the experiment. -/
  rightPublic : F.Carrier groupParameters

/-- The encoding of a blinded CDH input: the unary security parameter, the group parameters and
the words of the four elements, each framed except the last (`encBlindedCDHInput_apply`). -/
enc_structure encBlindedCDHInput (F : PrimeOrderGroupFamily) : BlindedCDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftBlind : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightBlind : (F.encode groupParameters) using (F.encode_injective groupParameters),
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- An adversary for the blinded CDH problem over the family: given the security parameter, the
group parameters and `a, b, u, v`, it answers an exponent and a group element. -/
abbrev BlindedCDHAdversary : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d → F.Carrier d →
    ProbComp (BlindedCDHAnswer (F.order d) (F.Carrier d))

variable {F} in
/-- A blinded CDH adversary is PPT when one uniform strict PPT machine reads `encBlindedCDHInput`
and writes the adversary's exponent as a binary number below the order, followed by the word of
its value. -/
@[expose] def BlindedCDHAdversary.IsPPT (adversary : F.BlindedCDHAdversary) : Prop :=
  IsPPTOn F.encBlindedCDHInput (encPair encNat encBits) fun x =>
    (fun out => (out.exponent.val, F.encode x.groupParameters out.value)) <$>
      adversary x.secParam x.groupParameters x.leftBlind x.rightBlind x.leftPublic x.rightPublic

/-- The blinded CDH game: choose group parameters with the setup law, then run
`Cslib.Crypto.blindedCDHExperiment` in that group. -/
@[expose] noncomputable def blindedCDHGame (setup : ℕ → PMF F.Desc)
    (adversary : F.BlindedCDHAdversary) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    blindedCDHExperiment (F.order d) (F.generator d) (adversary n d)

/-- The reduction of [BonehShoup2023], Lemma 21.7, as a CDH adversary: draw the two blinding
exponents with `sampleExp` and run `Cslib.Crypto.blindedCDHToCDHWith`. -/
noncomputable def blindedCDHToCDHAdversary (adversary : F.BlindedCDHAdversary) : F.CDHAdversary :=
  fun n d s t => do
    let μ ← F.sampleExp n d
    let ν ← F.sampleExp n d
    blindedCDHToCDHWith (F.order d) (F.generator d) (adversary n d) (μ : ZMod (F.order d))
      (ν : ZMod (F.order d)) s t

/-- What the reduction of Lemma 21.7 adds to the adversary's value, with every scalar a natural
number, as the machine computes it. -/
private def blindedCDHCorrection (d : F.Desc) (μ ν γ : ℕ) (s t : F.Carrier d) : F.Carrier d :=
  ((γ * ν : ℕ) : ZMod (F.order d)) • s + ((γ * μ : ℕ) : ZMod (F.order d)) • t +
    (((F.order d - 1) * (γ * γ * μ * ν) : ℕ) : ZMod (F.order d)) • F.generator d

private theorem solve_eq_add_blindedCDHCorrection (d : F.Desc)
    (out : BlindedCDHAnswer (F.order d) (F.Carrier d)) (μ ν : ℕ) (s t : F.Carrier d) :
    out.solve (F.generator d) (μ : ZMod (F.order d)) (ν : ZMod (F.order d)) s t =
      out.value + F.blindedCDHCorrection d μ ν out.exponent.val s t := by
  simp only [BlindedCDHAnswer.solve, blindedCDHCorrection, Nat.cast_mul, ZMod.natCast_zmod_val,
    ZMod.natCast_self_sub_one]
  module

variable {F} in
/-- **The reduction of [BonehShoup2023], Lemma 21.7, is efficient**: it is uniform strict PPT
whenever the adversary is. -/
theorem isPPT_blindedCDHToCDHAdversary {adversary : F.BlindedCDHAdversary}
    (hA : adversary.IsPPT) : (F.blindedCDHToCDHAdversary adversary).IsPPT := by
  -- the adversary's input, computed from the CDH input and the two draws
  let E := encPair (encPair F.encCDHInput encNat) encNat
  let prep : (F.CDHInput × ℕ) × ℕ → F.BlindedCDHInput := fun p =>
    { secParam := p.1.1.secParam
      groupParameters := p.1.1.groupParameters
      leftBlind := (p.1.2 : ZMod (F.order p.1.1.groupParameters)) • F.generator _
      rightBlind := (p.2 : ZMod (F.order p.1.1.groupParameters)) • F.generator _
      leftPublic := p.1.1.leftPublic
      rightPublic := p.1.1.rightPublic }
  have hx : ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.1.1) E F.encCDHInput := by
    fun_prop
  have hd := F.encCDHInput_groupParameters_polyTime hx
  have hg := computableInPolyTime_encode_generator hd
  have hprep : ComputableInPolyTime prep E F.encBlindedCDHInput :=
    F.encBlindedCDHInput_mk_polyTime (F.encCDHInput_secParam_polyTime hx) hd
      (computableInPolyTime_encode_natCast_smul hd
        (show ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.1.2) E encNat by fun_prop)
        hg)
      (computableInPolyTime_encode_natCast_smul hd
        (show ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.2) E encNat by fun_prop)
        hg)
      (F.encCDHInput_leftPublic_polyTime hx) (F.encCDHInput_rightPublic_polyTime hx)
  -- the output, computed from that input and the adversary's encoded answer
  let E' := encPair E (encPair encNat encBits)
  have hx' : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => p.1.1.1) E' F.encCDHInput := by fun_prop
  have hd' := F.encCDHInput_groupParameters_polyTime hx'
  have hμ : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => p.1.1.2) E' encNat := by fun_prop
  have hν : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => p.1.2) E' encNat := by fun_prop
  have hγ : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => p.2.1) E' encNat := by fun_prop
  have hw : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => p.2.2) E' encBits := by fun_prop
  have hcorr : ComputableInPolyTime
      (fun p : ((F.CDHInput × ℕ) × ℕ) × ℕ × List Bool => F.encode p.1.1.1.groupParameters
        (F.blindedCDHCorrection p.1.1.1.groupParameters p.1.1.2 p.1.2 p.2.1
          p.1.1.1.leftPublic p.1.1.1.rightPublic)) E' encBits :=
    computableInPolyTime_encode_add hd'
      (computableInPolyTime_encode_add hd'
        (computableInPolyTime_encode_natCast_smul hd' (hγ.binary_mul' hν)
          (F.encCDHInput_leftPublic_polyTime hx'))
        (computableInPolyTime_encode_natCast_smul hd' (hγ.binary_mul' hμ)
          (F.encCDHInput_rightPublic_polyTime hx')))
      (computableInPolyTime_encode_natCast_smul hd'
        (((F.computableInPolyTime_order.comp hd').binary_sub' (.const 1)).binary_mul'
          (((hγ.binary_mul' hγ).binary_mul' hμ).binary_mul' hν))
        (computableInPolyTime_encode_generator hd'))
  have hout := F.computableInPolyTime_add.comp (hd'.prod (hw.prod hcorr))
  have hprog : IsPPTOn F.encCDHInput encBits (fun x : F.CDHInput =>
      F.sampleExp x.secParam x.groupParameters >>= fun μ =>
        F.sampleExp x.secParam x.groupParameters >>= fun ν =>
          (fun o : ℕ × List Bool => F.add (x.groupParameters, o.2,
              F.encode x.groupParameters (F.blindedCDHCorrection x.groupParameters μ ν o.1
                x.leftPublic x.rightPublic))) <$>
            ((fun out : BlindedCDHAnswer (F.order x.groupParameters)
                  (F.Carrier x.groupParameters) =>
                (out.exponent.val, F.encode x.groupParameters out.value)) <$>
              adversary x.secParam x.groupParameters
                ((μ : ZMod (F.order x.groupParameters)) • F.generator x.groupParameters)
                ((ν : ZMod (F.order x.groupParameters)) • F.generator x.groupParameters)
                x.leftPublic x.rightPublic)) := by
    refine IsPPTOn.bind_with (F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)) ?_
    refine IsPPTOn.bind_with (F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)) ?_
    exact (hA.preprocess hprep).map_with hout
  refine hprog.congr fun x => ?_
  simp only [blindedCDHToCDHAdversary, blindedCDHToCDHWith, ProbComp.eval_bind,
    ProbComp.eval_map, ProbComp.eval_pure, PMF.map_bind, PMF.map_comp, PMF.pure_map,
    Function.comp_def, F.add_encode, solve_eq_add_blindedCDHCorrection]
  rfl

/-- **Sampling loss of the reduction of [BonehShoup2023], Lemma 21.7**: the blinded CDH game and
the CDH game of the reduction accept with probabilities at most `2 / 2 ^ n` apart, one `1 / 2 ^ n`
for each `sampleExp` draw. -/
theorem advantage_blindedCDHGame_cdhGame_le (setup : ℕ → PMF F.Desc)
    (adversary : F.BlindedCDHAdversary) (n : ℕ) :
    Game.advantage (F.blindedCDHGame setup adversary n)
      (F.cdhGame setup (F.blindedCDHToCDHAdversary adversary) n) ≤ 2 / 2 ^ n := by
  refine Game.advantage_withSetup_le _ _ _ fun d _ => ?_
  have hred : ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
        (F.blindedCDHToCDHAdversary adversary n d)) =
      (ProbComp.eval (F.sampleExp n d)).bind fun μ =>
        (ProbComp.eval (F.sampleExp n d)).bind fun ν =>
          ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
            (blindedCDHToCDHWith (F.order d) (F.generator d) (adversary n d)
              (μ : ZMod (F.order d)) (ν : ZMod (F.order d)))) := by
    refine (eval_cdhExperiment_bind _ _ (F.sampleExp n d) fun μ s t => do
      let ν ← F.sampleExp n d
      blindedCDHToCDHWith (F.order d) (F.generator d) (adversary n d) (μ : ZMod (F.order d))
        (ν : ZMod (F.order d)) s t).trans ?_
    refine congrArg (PMF.bind _) (funext fun μ => ?_)
    exact eval_cdhExperiment_bind _ _ (F.sampleExp n d) fun ν =>
      blindedCDHToCDHWith (F.order d) (F.generator d) (adversary n d) (μ : ZMod (F.order d))
        (ν : ZMod (F.order d))
  rw [Experiment.advantage, eval_blindedCDHExperiment, hred, Game.advantage_comm]
  exact F.advantage_bind_sampleExp_pair_le n d fun μ ν =>
    ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
      (blindedCDHToCDHWith (F.order d) (F.generator d) (adversary n d) μ ν))

/-- **[BonehShoup2023], Lemma 21.7**, Section 21.11.5, p. 910: under the CDH assumption, every PPT
adversary wins the blinded CDH game with negligible probability. -/
theorem CDH.negligible_blindedCDHGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.CDH setup) (adversary : F.BlindedCDHAdversary) (hA : adversary.IsPPT) :
    Negligible fun n => Game.succProbability (F.blindedCDHGame setup adversary n) := by
  have hcdh := h _ (F.isPPT_blindedCDHToCDHAdversary hA)
  negligible using fun n => Game.succProbability_le_add_of_advantage_le
    (F.advantage_blindedCDHGame_cdhGame_le setup adversary n)

/-! ### Lemma 21.8 -/

/-- The input of an adversary in the two-point blinded CDH game: the security parameter, public
group parameters and the three elements `a`, `b`, `u` of [BonehShoup2023], Lemma 21.8. -/
structure BlindedCDHPairInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group. -/
  groupParameters : F.Desc
  /-- The first blinding element, `a = α • g` in the experiment. -/
  leftBlind : F.Carrier groupParameters
  /-- The second blinding element, `b = β • g` in the experiment. -/
  rightBlind : F.Carrier groupParameters
  /-- The public element, `u = x • g` in the experiment. -/
  leftPublic : F.Carrier groupParameters

/-- The encoding of a two-point blinded CDH input: the unary security parameter, the group
parameters and the words of the three elements, each framed except the last
(`encBlindedCDHPairInput_apply`). -/
enc_structure encBlindedCDHPairInput (F : PrimeOrderGroupFamily) : BlindedCDHPairInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftBlind : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightBlind : (F.encode groupParameters) using (F.encode_injective groupParameters),
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- What a machine writes for a `Cslib.Crypto.BlindedCDHPairAnswer`: the two exponents as binary
numbers and the words of the three elements. -/
structure BlindedCDHPairAnswerWords where
  /-- The first exponent, as a number below the order. -/
  exponent₁ : ℕ
  /-- The second exponent, as a number below the order. -/
  exponent₂ : ℕ
  /-- The word of the adversary's `v`. -/
  right : List Bool
  /-- The word of the first value. -/
  value₁ : List Bool
  /-- The word of the second value. -/
  value₂ : List Bool

/-- The encoding of the written answer: the five fields in order, each framed except the last
(`encBlindedCDHPairAnswerWords_apply`). -/
enc_structure encBlindedCDHPairAnswerWords : BlindedCDHPairAnswerWords where
  exponent₁ : encNat, exponent₂ : encNat, right : encBits, value₁ : encBits, value₂ : encBits

/-- The written form of an answer in the group of `d`. -/
@[expose] def blindedCDHPairAnswerWords (d : F.Desc)
    (out : BlindedCDHPairAnswer (F.order d) (F.Carrier d)) : BlindedCDHPairAnswerWords where
  exponent₁ := out.exponent₁.val
  exponent₂ := out.exponent₂.val
  right := F.encode d out.right
  value₁ := F.encode d out.value₁
  value₂ := F.encode d out.value₂

/-- An adversary for the two-point blinded CDH problem over the family: given the security
parameter, the group parameters and `a, b, u`, it answers two exponents and three group
elements. -/
abbrev BlindedCDHPairAdversary : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d →
    ProbComp (BlindedCDHPairAnswer (F.order d) (F.Carrier d))

variable {F} in
/-- A two-point blinded CDH adversary is PPT when one uniform strict PPT machine reads
`encBlindedCDHPairInput` and writes the answer as `encBlindedCDHPairAnswerWords`. -/
@[expose] def BlindedCDHPairAdversary.IsPPT (adversary : F.BlindedCDHPairAdversary) : Prop :=
  IsPPTOn F.encBlindedCDHPairInput encBlindedCDHPairAnswerWords fun x =>
    F.blindedCDHPairAnswerWords x.groupParameters <$>
      adversary x.secParam x.groupParameters x.leftBlind x.rightBlind x.leftPublic

/-- The two-point blinded CDH game: choose group parameters with the setup law, then run
`Cslib.Crypto.blindedCDHPairExperiment` in that group. -/
@[expose] noncomputable def blindedCDHPairGame (setup : ℕ → PMF F.Desc)
    (adversary : F.BlindedCDHPairAdversary) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    blindedCDHPairExperiment (F.order d) (F.generator d) (adversary n d)

/-- The reduction of [BonehShoup2023], Lemma 21.8, as a CDH adversary: draw the blinding exponent
with `sampleExp` and run `Cslib.Crypto.blindedCDHPairToCDHWith`. -/
noncomputable def blindedCDHPairToCDHAdversary (adversary : F.BlindedCDHPairAdversary) :
    F.CDHAdversary :=
  fun n d s t => do
    let μ ← F.sampleExp n d
    blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d) (μ : ZMod (F.order d)) s t

/-- The inverse of `c - c'` modulo a prime `q` on natural numbers, `0` when `c ≡ c'`. The second
factor corrects `extractNat` at `q = 2`, where `0 ^ (q - 2) = 1`. -/
private def invSubNat (q c c' : ℕ) : ℕ :=
  extractNat q c 1 c' 0 * ((c + (q - 1) * c') * extractNat q c 1 c' 0)

private theorem invSubNat_cast {q : ℕ} [Fact q.Prime] (c c' : ℕ) :
    (invSubNat q c c' : ZMod q) = ((c : ZMod q) - c')⁻¹ := by
  have hsub : ((c + (q - 1) * c' : ℕ) : ZMod q) = (c : ZMod q) - c' := by
    rw [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self_sub_one]
    ring
  rw [invSubNat, Nat.cast_mul, Nat.cast_mul, hsub]
  by_cases h : (c : ZMod q) = c'
  · rw [h, sub_self, zero_mul, mul_zero, inv_zero]
  · rw [extractNat_cast h, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one,
      mul_inv_cancel₀ (sub_ne_zero.mpr h), mul_one]

private theorem pairSolve_eq (d : F.Desc) (out : BlindedCDHPairAnswer (F.order d) (F.Carrier d))
    (μ : ℕ) (s : F.Carrier d) :
    out.solve (μ : ZMod (F.order d)) s =
      (invSubNat (F.order d) out.exponent₁.val out.exponent₂.val : ZMod (F.order d)) •
          out.value₂ +
        ((invSubNat (F.order d) out.exponent₁.val out.exponent₂.val * (F.order d - 1) : ℕ) :
          ZMod (F.order d)) • out.value₁ +
        (((F.order d - 1) * μ : ℕ) : ZMod (F.order d)) • out.right +
        (((out.exponent₁.val + out.exponent₂.val) * μ : ℕ) : ZMod (F.order d)) • s := by
  simp only [BlindedCDHPairAnswer.solve, Nat.cast_mul, Nat.cast_add, invSubNat_cast,
    ZMod.natCast_zmod_val, ZMod.natCast_self_sub_one]
  module

variable {F} in
/-- **The reduction of [BonehShoup2023], Lemma 21.8, with its blinding exponent read from the
input, is efficient**: on a CDH input and a number `μ`, running
`Cslib.Crypto.blindedCDHPairToCDHWith` with the blinding exponent `μ` is uniform strict PPT
whenever the adversary is. `isPPT_blindedCDHPairToCDHAdversary` draws `μ` with `sampleExp`
first. -/
theorem isPPTOn_blindedCDHPairToCDHWith {adversary : F.BlindedCDHPairAdversary}
    (hA : adversary.IsPPT) :
    IsPPTOn (encPair F.encCDHInput encNat) encBits fun p : F.CDHInput × ℕ =>
      F.encode p.1.groupParameters <$>
        blindedCDHPairToCDHWith (F.order p.1.groupParameters) (F.generator p.1.groupParameters)
          (adversary p.1.secParam p.1.groupParameters) (p.2 : ZMod (F.order p.1.groupParameters))
          p.1.leftPublic p.1.rightPublic := by
  -- the adversary's input, computed from the CDH input and the exponent
  let E := encPair F.encCDHInput encNat
  let prep : F.CDHInput × ℕ → F.BlindedCDHPairInput := fun p =>
    { secParam := p.1.secParam
      groupParameters := p.1.groupParameters
      leftBlind := (p.2 : ZMod (F.order p.1.groupParameters)) • F.generator _
      rightBlind := p.1.leftPublic
      leftPublic := p.1.rightPublic }
  have hx : ComputableInPolyTime (fun p : F.CDHInput × ℕ => p.1) E F.encCDHInput := by fun_prop
  have hd := F.encCDHInput_groupParameters_polyTime hx
  have hprep : ComputableInPolyTime prep E F.encBlindedCDHPairInput :=
    F.encBlindedCDHPairInput_mk_polyTime (F.encCDHInput_secParam_polyTime hx) hd
      (computableInPolyTime_encode_natCast_smul hd
        (show ComputableInPolyTime (fun p : F.CDHInput × ℕ => p.2) E encNat by fun_prop)
        (computableInPolyTime_encode_generator hd))
      (F.encCDHInput_leftPublic_polyTime hx) (F.encCDHInput_rightPublic_polyTime hx)
  -- the output, computed from that input and the adversary's written answer
  let E' := encPair E encBlindedCDHPairAnswerWords
  have hx' : ComputableInPolyTime
      (fun p : (F.CDHInput × ℕ) × BlindedCDHPairAnswerWords => p.1.1) E' F.encCDHInput := by
    fun_prop
  have hd' := F.encCDHInput_groupParameters_polyTime hx'
  have hm := (F.computableInPolyTime_order.comp hd').binary_sub' (.const 1)
  have hμ : ComputableInPolyTime
      (fun p : (F.CDHInput × ℕ) × BlindedCDHPairAnswerWords => p.1.2) E' encNat := by fun_prop
  have hans : ComputableInPolyTime
      (fun p : (F.CDHInput × ℕ) × BlindedCDHPairAnswerWords => p.2) E'
      encBlindedCDHPairAnswerWords := by fun_prop
  have hγ₁ := encBlindedCDHPairAnswerWords_exponent₁_polyTime hans
  have hγ₂ := encBlindedCDHPairAnswerWords_exponent₂_polyTime hans
  have hex := computableInPolyTime_extractNat hd' hγ₁ (.const 1) hγ₂ (.const 0)
  have hinv : ComputableInPolyTime
      (fun p : (F.CDHInput × ℕ) × BlindedCDHPairAnswerWords =>
        invSubNat (F.order p.1.1.groupParameters) p.2.exponent₁ p.2.exponent₂) E' encNat :=
    hex.binary_mul' ((hγ₁.binary_add' (hm.binary_mul' hγ₂)).binary_mul' hex)
  have hout := F.computableInPolyTime_add.comp (hd'.prod
    ((F.computableInPolyTime_add.comp (hd'.prod
      ((F.computableInPolyTime_add.comp (hd'.prod
        ((F.computableInPolyTime_smul.comp (hd'.prod (hinv.prod
          (encBlindedCDHPairAnswerWords_value₂_polyTime hans)))).prod
        (F.computableInPolyTime_smul.comp (hd'.prod ((hinv.binary_mul' hm).prod
          (encBlindedCDHPairAnswerWords_value₁_polyTime hans))))))).prod
      (F.computableInPolyTime_smul.comp (hd'.prod ((hm.binary_mul' hμ).prod
        (encBlindedCDHPairAnswerWords_right_polyTime hans))))))).prod
    (computableInPolyTime_encode_natCast_smul hd' ((hγ₁.binary_add' hγ₂).binary_mul' hμ)
      (F.encCDHInput_leftPublic_polyTime hx'))))
  have hprog : IsPPTOn E encBits (fun p : F.CDHInput × ℕ =>
      (fun o : BlindedCDHPairAnswerWords => F.add (p.1.groupParameters,
          F.add (p.1.groupParameters,
            F.add (p.1.groupParameters,
              F.smul (p.1.groupParameters,
                invSubNat (F.order p.1.groupParameters) o.exponent₁ o.exponent₂, o.value₂),
              F.smul (p.1.groupParameters,
                invSubNat (F.order p.1.groupParameters) o.exponent₁ o.exponent₂ *
                  (F.order p.1.groupParameters - 1), o.value₁)),
            F.smul (p.1.groupParameters, (F.order p.1.groupParameters - 1) * p.2, o.right)),
          F.encode p.1.groupParameters
            ((((o.exponent₁ + o.exponent₂) * p.2 : ℕ) : ZMod (F.order p.1.groupParameters)) •
              p.1.leftPublic))) <$>
        (F.blindedCDHPairAnswerWords p.1.groupParameters <$>
          adversary p.1.secParam p.1.groupParameters
            ((p.2 : ZMod (F.order p.1.groupParameters)) • F.generator p.1.groupParameters)
            p.1.leftPublic p.1.rightPublic)) :=
    (hA.preprocess hprep).map_with hout
  refine hprog.congr fun p => ?_
  simp only [blindedCDHPairToCDHWith, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.map_bind, PMF.map_comp, PMF.pure_map, Function.comp_def, blindedCDHPairAnswerWords,
    F.smul_encode, F.add_encode, pairSolve_eq]
  rfl

variable {F} in
/-- **The reduction of [BonehShoup2023], Lemma 21.8, is efficient**: it is uniform strict PPT
whenever the adversary is. -/
theorem isPPT_blindedCDHPairToCDHAdversary {adversary : F.BlindedCDHPairAdversary}
    (hA : adversary.IsPPT) : (F.blindedCDHPairToCDHAdversary adversary).IsPPT := by
  have hprog : IsPPTOn F.encCDHInput encBits (fun x : F.CDHInput =>
      F.sampleExp x.secParam x.groupParameters >>= fun μ =>
        F.encode x.groupParameters <$>
          blindedCDHPairToCDHWith (F.order x.groupParameters) (F.generator x.groupParameters)
            (adversary x.secParam x.groupParameters) (μ : ZMod (F.order x.groupParameters))
            x.leftPublic x.rightPublic) :=
    IsPPTOn.bind_with (F.isPPTOn_sampleExp (by fun_prop) (by fun_prop))
      (isPPTOn_blindedCDHPairToCDHWith hA)
  refine hprog.congr fun x => ?_
  simp only [blindedCDHPairToCDHAdversary, map_bind]

/-- **Sampling loss of the reduction of [BonehShoup2023], Lemma 21.8**: the two-point blinded CDH
game is won at most as often as the CDH game of the reduction, up to `1 / 2 ^ n` for its one
`sampleExp` draw. -/
theorem succProbability_blindedCDHPairGame_le (setup : ℕ → PMF F.Desc)
    (adversary : F.BlindedCDHPairAdversary) (n : ℕ) :
    Game.succProbability (F.blindedCDHPairGame setup adversary n) ≤
      Game.succProbability (F.cdhGame setup (F.blindedCDHPairToCDHAdversary adversary) n) +
        1 / 2 ^ n := by
  have h₁ : Game.succProbability (F.blindedCDHPairGame setup adversary n) ≤
      Game.succProbability ((setup n).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun μ =>
          ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
            (blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d) μ))) :=
    Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ =>
      eval_blindedCDHPairExperiment_true_le _ _ _)
  have h₂ : Game.advantage ((setup n).bind fun d =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun μ =>
          ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
            (blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d) μ)))
      (F.cdhGame setup (F.blindedCDHPairToCDHAdversary adversary) n) ≤ 1 / 2 ^ n := by
    refine Game.advantage_bind_le_of_support (setup n) _ _ fun d _ => ?_
    have hred : ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
          (F.blindedCDHPairToCDHAdversary adversary n d)) =
        (ProbComp.eval (F.sampleExp n d)).bind fun μ =>
          ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
            (blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d)
              (μ : ZMod (F.order d)))) :=
      eval_cdhExperiment_bind _ _ (F.sampleExp n d) fun μ =>
        blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d)
          (μ : ZMod (F.order d))
    rw [hred, Game.advantage_comm]
    exact F.advantage_bind_sampleExp_le n d fun μ =>
      ProbComp.eval (cdhExperiment (F.order d) (F.generator d)
        (blindedCDHPairToCDHWith (F.order d) (F.generator d) (adversary n d) μ))
  exact h₁.trans (Game.succProbability_le_add_of_advantage_le h₂)

/-- **[BonehShoup2023], Lemma 21.8**, Section 21.11.5, p. 911: under the CDH assumption, every PPT
adversary wins the two-point blinded CDH game with negligible probability. -/
theorem CDH.negligible_blindedCDHPairGame {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (h : F.CDH setup) (adversary : F.BlindedCDHPairAdversary) (hA : adversary.IsPPT) :
    Negligible fun n => Game.succProbability (F.blindedCDHPairGame setup adversary n) := by
  have hcdh := h _ (F.isPPT_blindedCDHPairToCDHAdversary hA)
  negligible using F.succProbability_blindedCDHPairGame_le setup adversary

end Cslib.Crypto.PrimeOrderGroupFamily
