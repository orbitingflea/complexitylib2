/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Retry
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Crypto.Computational.DiffieHellman.SelfReduction
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.Nat.Bits
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Languages.Probabilistic.Retry
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.Negligible

/-!
# The DL and CDH self-reductions over a prime-order group family

[BonehShoup2023], Section 10.5.1, turns an efficient algorithm `A` that finds the discrete logarithm
of a random element of a fixed group with probability `ε` into an efficient algorithm `B` that,
on every input, outputs `fail` or the discrete logarithm and outputs the latter with probability
`ε` (Theorem 10.2), and Exercise 10.6 asks for the same for CDH. The fixed-group module
`CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction.lean` computes the exact output
probabilities of these algorithms with uniform masks and no cost model. This module states them
as adversaries over a `PrimeOrderGroupFamily`, proves that they are uniform strict PPT whenever
`A` is, and derives the family-level consequences.

Here `ε` is `dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary A n d)`, the success
probability of the word-level adversary `A` read in the group selected by `d`
(`succProbability_discreteLogGame_pure`). Footnote 1 of the book (p. 411) fixes the group in the
same way.

* `dlSelfReduceAdversary A` masks the input word by `σ • g` with `F.add` and `F.smul`, runs `A`
  and subtracts `σ` from the answer read as a natural number; its answer is never the empty word.
  `dlSelfReduceRetryAdversary A k` makes at most `k n` such calls, each followed by the test
  `x • g = u`, computed on encodings by comparing `F.smul (d, x, encode g)` with the input word,
  and returns the first answer that passes the test, or the empty word. With `k = fun _ => 1` it
  is the algorithm `B` of the proof of Theorem 10.2 (p. 412), with the empty word for `fail`.
* `cdhSelfReduceAdversary A` masks both inputs and removes the three cross terms, as
  `Cslib.Crypto.cdhSelfReduce` does; the construction is this library's, since Exercise 10.6 gives
  none.

The reduction reads only words: on every input word its certificates hold, and the loop's test
rejects every word that encodes no group element
(`eq_nil_of_mem_support_dlSelfReduceRetryAdversary_of_not_mem_range`).

## Differences from the book

* The masks are drawn by `sampleExp`, which is within statistical distance `1 / 2 ^ n` of uniform
  on `ZMod q`, not uniform. So the family-level success probabilities are bounded below by `ε`
  less `1 / 2 ^ n` (one DL mask) or `2 / 2 ^ n` (two CDH masks), not equal to `ε` as in
  Theorem 10.2. The equality holds for the fixed-group programs with uniform masks
  (`Cslib.Crypto.eval_dlSelfReduce_one_smul_some`).
* The book's `fail` is the empty word. The discrete-logarithm game reads it as the exponent `0`,
  so on the instance `α = 0` the game counts a failed run as a win. The bounds for the checked
  loop are therefore stated on the output word, for the event that it is nonempty and reads as
  `α`; the bounds on the exponent that the game reads are corollaries.
* The answer `x - σ` is computed on natural numbers as `x + (q - σ % q)`, which the game reads
  modulo `q`.
* The iteration remark after Theorem 10.2 runs `B` `n ⌈1 / ε⌉` times. A uniform machine is given
  a bound `invEps n` with `1 / invEps n ≤ ε` instead of `ε`, and runs `n * (2 * invEps n)`
  attempts: the factor `2` pays for the sampling loss.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.encDiscreteLogInput`: the input encoding of a word-level
  discrete-logarithm adversary, as in `DiscreteLog`.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlSelfReduceAdversary`: one masked call of a word-level
  discrete-logarithm adversary.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlSelfReduceRetryAdversary`: at most `k n` checked attempts.
* `Cslib.Crypto.PrimeOrderGroupFamily.cdhSelfReduceAdversary`: one call of a CDH adversary with
  both inputs masked.
* `Cslib.Crypto.PrimeOrderGroupFamily.dlWorstCaseGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.cdhWorstCaseGame`: the adversary against fixed instances
  `α d • g` (and `β d • g`) in groups drawn by the setup law.

## Main results

* Certificates: `isPPTOn_dlSelfReduceAdversary`, `isPPTOn_dlSelfReduceRetryAdversary`,
  `isPPTOn_dlSelfReduceRetryAdversary_invEps` and `isPPT_cdhSelfReduceAdversary`, each from the
  certificate of the input adversary; the two loop certificates also take an attempt count `k`,
  or a bound `invEps`, computable in polynomial time in unary.
* `eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary`: on every input word the
  loop outputs the empty word or a word `x` with `encode (x • g)` equal to the input
  (Theorem 10.2: "`B` outputs `fail` or `Dlog_g(u)`").
* `le_toOuterMeasure_dlSelfReduceRetryAdversary_one`: on the encoding of every instance `α • g`,
  one checked attempt returns a nonempty word that reads as `α` with probability at least
  `ε - 1 / 2 ^ n` (Theorem 10.2, with the sampling loss), and
  `one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary` for `k n` attempts. The
  corresponding bounds on the exponent that the game reads are
  `le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one` and
  `one_sub_pow_le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary`.
* `dlSelfReduceRetryAdversary_error_le_pow` and `negligible_dlSelfReduceRetryAdversary_error`: the
  iteration remark. If the adversary wins in the group with probability at least `1 / invEps n`
  and `1 / 2 ^ n ≤ 1 / (2 * invEps n)`, the loop with `n * (2 * invEps n)` attempts errs, that
  is returns the empty word or a word that does not read as `α`, with probability at most
  `(1 / 2) ^ n` on every instance. So it errs with negligible probability when `invEps` is
  computable in polynomial time in unary and, for all large `n`, `0 < invEps n` and the adversary
  wins with probability at least `1 / invEps n`.
  `discreteLogAdversary_dlSelfReduceRetryAdversary_error_le_pow` and
  `negligible_discreteLogAdversary_dlSelfReduceRetryAdversary_error` bound the probability that
  the game reads an exponent other than `α`.
* `advantage_dlWorstCaseGame_discreteLogGame_le` and `discreteLog_of_worstCase`: the reduction
  wins the worst-case game within `1 / 2 ^ n` of the adversary's average-case success, so
  `DiscreteLog` holds if every PPT adversary has instances on which it succeeds with negligible
  probability.
* `advantage_cdhSelfReduceAdversary_le`, `advantage_cdhWorstCaseGame_cdhGame_le` and
  `cdh_of_worstCase`: the same for CDH with loss `2 / 2 ^ n` (Exercise 10.6, with the sampling
  loss).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section
  10.5.1: Theorem 10.2, the remark after it and its proof (pp. 411–412); Exercise 10.6 (p. 425).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### The programs -/

/-- The input `(n, d, w)` of a word-level discrete-logarithm adversary: the security parameter in
unary and the group parameters, each framed, then the instance word. It is the input encoding in
`DiscreteLog`. -/
abbrev encDiscreteLogInput : ℕ × F.Desc × List Bool ↪ List Bool :=
  encPair encUnary (encPair F.encDesc encBits)

/-- One masked call of a word-level discrete-logarithm adversary on the input word `x.2`: draw
`σ` with `sampleExp`, run the adversary on `x.2 + σ • g` computed with `F.add` and `F.smul`, and
subtract `σ` from its answer as natural numbers, `ofBits answer + (q - σ % q)`, which the game
reads modulo `q`. -/
noncomputable def dlSelfReduceAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) :
    ℕ → F.Desc × List Bool → ProbComp (List Bool) := fun n x => do
  let σ ← F.sampleExp n x.1
  let guess ← adversary n
    (x.1, F.add (x.1, x.2, F.smul (x.1, σ, F.encode x.1 (F.generator x.1))))
  return Nat.bits (ofBits guess + (F.order x.1 - σ % F.order x.1))

/-- One checked attempt: the answer word of `dlSelfReduceAdversary`, paired with the bit of the
test `x • g = u` computed on encodings, `F.smul (d, x, encode g) = w` for the input word `w`. -/
private noncomputable def dlSelfReduceAttempt
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ)
    (x : F.Desc × List Bool) : ProbComp (Bool × List Bool) :=
  (fun out => (decide (F.smul (x.1, ofBits out, F.encode x.1 (F.generator x.1)) = x.2), out)) <$>
    F.dlSelfReduceAdversary adversary n x

/-- At most `k n` checked attempts, each a masked call (`dlSelfReduceAdversary`) followed by the
test `x • g = u` computed on encodings, returning the first answer that passes its test, or the
empty word when none does. With `k = fun _ => 1` this is the algorithm `B` in the proof of
[BonehShoup2023], Theorem 10.2 (p. 412), with the empty word for its output `fail`. -/
noncomputable def dlSelfReduceRetryAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (k : ℕ → ℕ) :
    ℕ → F.Desc × List Bool → ProbComp (List Bool) := fun n x =>
  (fun o : Option (Bool × List Bool) => (o.getD (false, [])).2) <$>
    OracleComp.retry (fun p : Bool × List Bool => p.1) (F.dlSelfReduceAttempt adversary n x) (k n)

/-- One call of a CDH adversary with both inputs masked: draw `ρ` and `τ` with `sampleExp`, run
the adversary on `(u + ρ • g, v + τ • g)` and subtract `τ • u + ρ • v + (ρ * τ) • g`, as
`Cslib.Crypto.cdhSelfReduce` does with uniform masks. [BonehShoup2023], Exercise 10.6 (p. 425)
gives no construction; this one is this library's. -/
noncomputable def cdhSelfReduceAdversary (adversary : F.CDHAdversary) : F.CDHAdversary :=
  fun n d u v => do
    let ρ ← F.sampleExp n d
    let τ ← F.sampleExp n d
    let w ← adversary n d (u + (ρ : ZMod (F.order d)) • F.generator d)
      (v + (τ : ZMod (F.order d)) • F.generator d)
    return w - (τ : ZMod (F.order d)) • u - (ρ : ZMod (F.order d)) • v -
      ((ρ : ZMod (F.order d)) * τ) • F.generator d

/-- The worst-case discrete-logarithm game for the instances `α d • g`: draw group parameters `d`
with the setup law and run the word-level adversary on the encoding of `α d • g`. It wins when its
answer, read as an exponent, is `α d`. This game is this library's. -/
@[expose] noncomputable def dlWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α : ∀ d : F.Desc, ZMod (F.order d))
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => (fun x => decide (x = α d)) <$>
    F.discreteLogAdversary adversary n d (α d • F.generator d)

/-- The worst-case CDH game for the instance pairs `(α d • g, β d • g)`: draw group parameters `d`
with the setup law and run the CDH adversary on the pair. It wins when it outputs
`(α d * β d) • g`. This game is this library's. -/
@[expose] noncomputable def cdhWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α β : ∀ d : F.Desc, ZMod (F.order d)) (adversary : F.CDHAdversary) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => (fun w => decide (w = (α d * β d) • F.generator d)) <$>
    adversary n d (α d • F.generator d) (β d • F.generator d)

/-! ### Certificates -/

/-- **The masked call is efficient**: if the word-level adversary is uniform strict PPT, so is
`dlSelfReduceAdversary`. -/
theorem isPPTOn_dlSelfReduceAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn F.encDiscreteLogInput encBits fun input => adversary input.1 input.2) :
    IsPPTOn F.encDiscreteLogInput encBits
      (fun input => F.dlSelfReduceAdversary adversary input.1 input.2) := by
  refine IsPPTOn.bind_with (F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)) ?_
  refine ((hA.preprocess (prepare := fun p : (ℕ × F.Desc × List Bool) × ℕ =>
      (p.1.1, p.1.2.1, F.add (p.1.2.1, p.1.2.2,
        F.smul (p.1.2.1, p.2, F.encode p.1.2.1 (F.generator p.1.2.1)))))
      ?_).map_with
    (f := fun p guess => Nat.bits (ofBits guess + (F.order p.1.2.1 - p.2 % F.order p.1.2.1)))
    ?_).congr fun x => ?_
  · have hd : ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × ℕ => p.1.2.1)
        (encPair F.encDiscreteLogInput encNat) F.encDesc := by fun_prop
    have hsm := F.computableInPolyTime_smul.comp
      (hd.prod ((show ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × ℕ => p.2)
        (encPair F.encDiscreteLogInput encNat) encNat by fun_prop).prod
        (computableInPolyTime_encode_generator hd)))
    have hadd := F.computableInPolyTime_add.comp
      (hd.prod ((show ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × ℕ => p.1.2.2)
        (encPair F.encDiscreteLogInput encNat) encBits by fun_prop).prod
        hsm))
    exact (show ComputableInPolyTime (fun p : (ℕ × F.Desc × List Bool) × ℕ => p.1.1)
        (encPair F.encDiscreteLogInput encNat) encUnary by fun_prop).prod
      (hd.prod hadd)
  · have hbits : ComputableInPolyTime Nat.bits encNat encBits := .of_eq fun _ => rfl
    have hq := F.computableInPolyTime_order.comp
      (show ComputableInPolyTime
        (fun pair : ((ℕ × F.Desc × List Bool) × ℕ) × List Bool => pair.1.1.2.1)
        (encPair (encPair F.encDiscreteLogInput encNat) encBits)
        F.encDesc by fun_prop)
    have hσ : ComputableInPolyTime
        (fun pair : ((ℕ × F.Desc × List Bool) × ℕ) × List Bool => pair.1.2)
        (encPair (encPair F.encDiscreteLogInput encNat) encBits)
        encNat := by fun_prop
    have hguess : ComputableInPolyTime
        (fun pair : ((ℕ × F.Desc × List Bool) × ℕ) × List Bool => ofBits pair.2)
        (encPair (encPair F.encDiscreteLogInput encNat) encBits)
        encNat := by fun_prop
    exact hbits.comp (hguess.binary_add' (hq.binary_sub' (hσ.binary_mod' hq)))
  · simp

/-- **The checked loop is efficient**: if the word-level adversary is uniform strict PPT and the
number of attempts `k n` is computable in polynomial time in unary, `dlSelfReduceRetryAdversary`
is uniform strict PPT. -/
theorem isPPTOn_dlSelfReduceRetryAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn F.encDiscreteLogInput encBits fun input => adversary input.1 input.2)
    {k : ℕ → ℕ} (hk : ComputableInPolyTime k encUnary encUnary) :
    IsPPTOn F.encDiscreteLogInput encBits
      (fun input => F.dlSelfReduceRetryAdversary adversary k input.1 input.2) := by
  have hd : ComputableInPolyTime (fun pair : (ℕ × F.Desc × List Bool) × List Bool => pair.1.2.1)
      (encPair F.encDiscreteLogInput encBits) F.encDesc := by fun_prop
  have hsm := F.computableInPolyTime_smul.comp
    (hd.prod ((show ComputableInPolyTime
        (fun pair : (ℕ × F.Desc × List Bool) × List Bool => ofBits pair.2)
        (encPair F.encDiscreteLogInput encBits) encNat by fun_prop).prod
      (computableInPolyTime_encode_generator hd)))
  have hattempt : IsPPTOn F.encDiscreteLogInput (encPair encBool encBits)
      (fun input => F.dlSelfReduceAttempt adversary input.1 input.2) :=
    ((F.isPPTOn_dlSelfReduceAdversary hA).map_with
      (f := fun input out => (decide (F.smul (input.2.1, ofBits out,
        F.encode input.2.1 (F.generator input.2.1)) = input.2.2), out))
      (by fun_prop)).congr fun _ => rfl
  have hfuel : ComputableInPolyTime (fun input : ℕ × F.Desc × List Bool => k input.1)
      F.encDiscreteLogInput encUnary := hk.comp (by fun_prop)
  exact ((hattempt.retry (good := Prod.fst) (by fun_prop) hfuel).map
    (f := fun o : Option (Bool × List Bool) => (o.getD (false, [])).2)
    (by fun_prop)).congr fun _ => rfl

/-- The loop with `n * (2 * invEps n)` attempts, the count of
`negligible_dlSelfReduceRetryAdversary_error`, is uniform strict PPT when `invEps` is computable
in polynomial time in unary. -/
theorem isPPTOn_dlSelfReduceRetryAdversary_invEps
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn F.encDiscreteLogInput encBits fun input => adversary input.1 input.2)
    {invEps : ℕ → ℕ} (hinvEps : ComputableInPolyTime invEps encUnary encUnary) :
    IsPPTOn F.encDiscreteLogInput encBits
      (fun input => F.dlSelfReduceRetryAdversary adversary (fun n => n * (2 * invEps n))
        input.1 input.2) :=
  F.isPPTOn_dlSelfReduceRetryAdversary hA (by fun_prop)

/-- The CDH correction term computed with natural-number scalars, `q - σ % q` for `-σ`, is the
one of `cdhSelfReduceAdversary`. -/
private theorem add_correction_eq (d : F.Desc) (u v w : F.Carrier d) (ρ τ : ℕ) :
    w + ((((F.order d - τ % F.order d : ℕ) : ZMod (F.order d)) • u +
        ((F.order d - ρ % F.order d : ℕ) : ZMod (F.order d)) • v) +
        (((F.order d - ρ % F.order d : ℕ) : ZMod (F.order d)) * (τ : ZMod (F.order d))) •
          F.generator d) =
      w - (τ : ZMod (F.order d)) • u - (ρ : ZMod (F.order d)) • v -
        ((ρ : ZMod (F.order d)) * τ) • F.generator d := by
  rw [ZMod.natCast_sub_mod_eq_neg, ZMod.natCast_sub_mod_eq_neg]
  module

/-- **The CDH self-reduction is efficient**: if the CDH adversary is uniform strict PPT, so is
`cdhSelfReduceAdversary`. -/
theorem isPPT_cdhSelfReduceAdversary {adversary : F.CDHAdversary} (hA : adversary.IsPPT) :
    (F.cdhSelfReduceAdversary adversary).IsPPT := by
  have hs {α : Type} {enc : α ↪ List Bool} {x : α → F.CDHInput}
      (hx : ComputableInPolyTime x enc F.encCDHInput) :
      IsPPTOn enc encNat fun a => F.sampleExp (x a).secParam (x a).groupParameters :=
    F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)
  let E := encPair (encPair F.encCDHInput encNat) encNat
  have hx : ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.1.1) E F.encCDHInput := by
    fun_prop
  have hd := F.encCDHInput_groupParameters_polyTime hx
  have hn := F.encCDHInput_secParam_polyTime hx
  have hu := F.encCDHInput_leftPublic_polyTime hx
  have hv := F.encCDHInput_rightPublic_polyTime hx
  have hρ : ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.1.2) E encNat := by fun_prop
  have hτ : ComputableInPolyTime (fun p : (F.CDHInput × ℕ) × ℕ => p.2) E encNat := by fun_prop
  have hg := computableInPolyTime_encode_generator hd
  have hq := F.computableInPolyTime_order.comp hd
  have hcall := IsPPTOn.preprocess hA (F.encCDHInput_mk_polyTime hn hd
    (computableInPolyTime_encode_add hd hu (computableInPolyTime_encode_natCast_smul hd hρ hg))
    (computableInPolyTime_encode_add hd hv (computableInPolyTime_encode_natCast_smul hd hτ hg)))
  have hnegτ := hq.binary_sub' (hτ.binary_mod' hq)
  have hnegρ := hq.binary_sub' (hρ.binary_mod' hq)
  have hcorr := computableInPolyTime_encode_add hd (computableInPolyTime_encode_add hd
    (computableInPolyTime_encode_natCast_smul hd hnegτ hu)
    (computableInPolyTime_encode_natCast_smul hd hnegρ hv))
    (computableInPolyTime_encode_natCast_smul hd (hnegρ.binary_mul' hτ) hg)
  have hfst : ComputableInPolyTime (fun pair : ((F.CDHInput × ℕ) × ℕ) × List Bool => pair.1)
      (encPair E encBits) E := by fun_prop
  have hsnd : ComputableInPolyTime (fun pair : ((F.CDHInput × ℕ) × ℕ) × List Bool => pair.2)
      (encPair E encBits) encBits := by fun_prop
  have key : IsPPTOn F.encCDHInput encBits fun x : F.CDHInput =>
      F.sampleExp x.secParam x.groupParameters >>= fun ρ =>
      F.sampleExp x.secParam x.groupParameters >>= fun τ =>
      (fun z => F.add (x.groupParameters, z, F.encode x.groupParameters
        ((((F.order x.groupParameters - τ % F.order x.groupParameters : ℕ) :
            ZMod (F.order x.groupParameters)) • x.leftPublic +
          ((F.order x.groupParameters - ρ % F.order x.groupParameters : ℕ) :
            ZMod (F.order x.groupParameters)) • x.rightPublic) +
          (((F.order x.groupParameters - ρ % F.order x.groupParameters) * τ : ℕ) :
            ZMod (F.order x.groupParameters)) • F.generator x.groupParameters))) <$>
        (F.encode x.groupParameters <$> adversary x.secParam x.groupParameters
          (x.leftPublic + (ρ : ZMod (F.order x.groupParameters)) • F.generator x.groupParameters)
          (x.rightPublic +
            (τ : ZMod (F.order x.groupParameters)) • F.generator x.groupParameters)) := by
    refine IsPPTOn.bind_with (hs .id') ?_
    refine IsPPTOn.bind_with (hs (by fun_prop)) ?_
    exact hcall.map_with
      (F.computableInPolyTime_add.comp ((hd.comp hfst).prod (hsnd.prod (hcorr.comp hfst))))
  refine key.congr fun x => ?_
  simp [cdhSelfReduceAdversary, F.add_encode, F.add_correction_eq]

/-! ### One masked call -/

/-- On the encoding of an element `u`, the word-level masked call is one masked call of the
fixed-group adversary `F.discreteLogAdversary adversary n d`, with the mask drawn by `sampleExp`
in place of the uniform mask of `Cslib.Crypto.dlRerandomize`. -/
theorem discreteLogAdversary_dlSelfReduceAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (u : F.Carrier d) :
    F.discreteLogAdversary (F.dlSelfReduceAdversary adversary) n d u = do
      let σ ← F.sampleExp n d
      let α₁ ← F.discreteLogAdversary adversary n d (u + (σ : ZMod (F.order d)) • F.generator d)
      return α₁ - (σ : ZMod (F.order d)) := by
  simp [discreteLogAdversary, dlSelfReduceAdversary, F.smul_encode, F.add_encode,
    ZMod.natCast_sub_mod_eq_neg, ofBits_bits, ← sub_eq_add_neg]

/-- **One masked call on every instance**: on `α • g`, the masked call returns `α` with the
probability with which the adversary wins the discrete-logarithm experiment in the group `d`, up
to `1 / 2 ^ n`, the sampling loss of `sampleExp`. With a uniform mask the two are equal
(`Cslib.Crypto.eval_dlRerandomize_smul_apply`). -/
theorem advantage_dlSelfReduceAdversary_le
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    Experiment.advantage
      ((fun x => decide (x = α)) <$>
        F.discreteLogAdversary (F.dlSelfReduceAdversary adversary) n d (α • F.generator d))
      (dlExperiment (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d)) ≤
      1 / 2 ^ n := by
  let k : ZMod (F.order d) → Game := fun σ =>
    ProbComp.eval ((fun x => decide (x - σ = α)) <$>
      F.discreteLogAdversary adversary n d (α • F.generator d + σ • F.generator d))
  have h1 : ProbComp.eval ((fun x => decide (x = α)) <$>
        F.discreteLogAdversary (F.dlSelfReduceAdversary adversary) n d (α • F.generator d)) =
      (ProbComp.eval (F.sampleExp n d)).bind fun s => k (s : ZMod (F.order d)) := by
    rw [discreteLogAdversary_dlSelfReduceAdversary]
    simp [k]
  have h2 : (PMF.uniformOfFintype (ZMod (F.order d))).bind k =
      (ProbComp.eval (dlRerandomize (F.order d) (F.generator d)
        (F.discreteLogAdversary adversary n d) (α • F.generator d))).map
        fun x => decide (x = α) := by
    simp [k, dlRerandomize, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h3 : Game.succProbability ((PMF.uniformOfFintype (ZMod (F.order d))).bind k) =
      Game.succProbability (ProbComp.eval
        (dlExperiment (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d))) := by
    rw [h2, Game.succProbability, Probability.PMF.map_decide_eq_apply_true,
      eval_dlRerandomize_smul_apply]
  have h := F.advantage_bind_sampleExp_le n d k
  rw [Experiment.advantage, h1]
  rwa [Game.advantage, h3] at h

/-! ### Worst case against average case, discrete logarithm -/

/-- In the group selected by `d`, the discrete-logarithm game with the constant setup law is the
fixed-group experiment: its success probability is the `ε` of [BonehShoup2023], Theorem 10.2, for
the adversary read in `d`. -/
theorem succProbability_discreteLogGame_pure
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc) :
    Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) adversary n) =
      dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) := by
  rw [discreteLogGame_eq]
  simp [Game.withSetup, dlAdvantage, Experiment.succProbability]

/-- The masked call wins the worst-case game on the instances `α d • g` within `1 / 2 ^ n` of the
adversary's success in the average-case game, for every setup law. -/
theorem advantage_dlWorstCaseGame_discreteLogGame_le (setup : ℕ → PMF F.Desc)
    (α : ∀ d : F.Desc, ZMod (F.order d))
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.advantage (F.dlWorstCaseGame setup α (F.dlSelfReduceAdversary adversary) n)
      (F.discreteLogGame setup adversary n) ≤ 1 / 2 ^ n := by
  rw [discreteLogGame_eq]
  exact Game.advantage_withSetup_le _ _ _ fun d _ =>
    F.advantage_dlSelfReduceAdversary_le adversary n d (α d)

/-- The adversary's average-case success is at most the masked call's worst-case success plus
`1 / 2 ^ n`. -/
theorem succProbability_discreteLogGame_le_dlWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α : ∀ d : F.Desc, ZMod (F.order d))
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) :
    Game.succProbability (F.discreteLogGame setup adversary n) ≤
      Game.succProbability (F.dlWorstCaseGame setup α (F.dlSelfReduceAdversary adversary) n) +
        1 / 2 ^ n := by
  refine Game.succProbability_le_add_of_advantage_le ?_
  rw [Game.advantage_comm]
  exact F.advantage_dlWorstCaseGame_discreteLogGame_le setup α adversary n

/-- Average-case discrete-logarithm hardness from worst-case hardness: if for every uniform strict
PPT word-level adversary there are instances `α d • g` on which it wins the worst-case game with
negligible probability, then `DiscreteLog` holds for the setup law. The instances may depend on
the adversary. The book states this implication only informally (p. 412: "if it is hard in the
worst case, then it must be hard on average"); this formulation and `dlWorstCaseGame` are this
library's. The premise of `Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_worstCase` is stronger: it
fixes the instances before the distinguisher. -/
theorem discreteLog_of_worstCase {setup : ℕ → PMF F.Desc}
    (hworst : ∀ adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool),
      IsPPTOn F.encDiscreteLogInput encBits (fun input => adversary input.1 input.2) →
      ∃ α : ∀ d : F.Desc, ZMod (F.order d),
        Negligible fun n => Game.succProbability (F.dlWorstCaseGame setup α adversary n)) :
    F.DiscreteLog setup := by
  intro adversary hA
  obtain ⟨α, hw⟩ := hworst _ (F.isPPTOn_dlSelfReduceAdversary hA)
  negligible using F.succProbability_discreteLogGame_le_dlWorstCaseGame setup α adversary

/-! ### The checked loop -/

/-- An answer that the loop can return is nonempty and passes its test: on the input word `w`, it
reads as an exponent `x` with `F.encode d (x • g) = w`. It is nonempty because the masked call
answers `Nat.bits (ofBits guess + (q - σ % q))` and `q - σ % q` is positive. -/
private theorem ne_nil_and_encode_smul_eq_of_mem_support_retry
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {k n : ℕ} {d : F.Desc}
    {w : List Bool} {b : Bool} {out : List Bool}
    (hout : some (b, out) ∈ (ProbComp.eval (OracleComp.retry (fun p : Bool × List Bool => p.1)
      (F.dlSelfReduceAttempt adversary n (d, w)) k)).support) :
    out ≠ [] ∧ F.encode d ((ofBits out : ZMod (F.order d)) • F.generator d) = w := by
  rw [ProbComp.support_eval] at hout
  obtain ⟨hb, hmem⟩ := OracleComp.mem_supportWith_retry hout
  obtain ⟨out', hout', hw⟩ := OracleComp.mem_supportWith_map_iff.mp hmem
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  refine ⟨?_, ?_⟩
  · simp only [dlSelfReduceAdversary, OracleComp.mem_supportWith_bind_iff,
      OracleComp.supportWith_pure, Set.mem_singleton_iff] at hout'
    obtain ⟨σ, -, guess, -, rfl⟩ := hout'
    have hσ := Nat.mod_lt σ (F.prime_order d).pos
    rw [Ne, Nat.bits_eq_nil_iff]
    omega
  · have htest : F.smul (d, ofBits out', F.encode d (F.generator d)) = w := by simpa using hb
    rwa [F.smul_encode] at htest

/-- **Soundness of the loop on every input word**: on `(d, w)` the loop outputs the empty word
(the book's `fail`) or a word that reads as an exponent `x` with `F.encode d (x • g) = w`. This is
the claim of [BonehShoup2023], Theorem 10.2 (pp. 411–412), that `B` outputs `fail` or
`Dlog_g(u)`, for any number of attempts. -/
theorem eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {k : ℕ → ℕ} {n : ℕ} {d : F.Desc}
    {w out : List Bool}
    (hout : out ∈ (ProbComp.eval (F.dlSelfReduceRetryAdversary adversary k n (d, w))).support) :
    out = [] ∨ F.encode d ((ofBits out : ZMod (F.order d)) • F.generator d) = w := by
  rw [dlSelfReduceRetryAdversary, ProbComp.eval_map, PMF.support_map] at hout
  obtain ⟨o, ho, rfl⟩ := hout
  obtain _ | ⟨b, out⟩ := o
  · exact Or.inl rfl
  · exact Or.inr (F.ne_nil_and_encode_smul_eq_of_mem_support_retry ho).2

/-- On the encoding of an element `u`, the loop outputs the empty word or a discrete logarithm of
`u`. -/
theorem eq_nil_or_smul_eq_of_mem_support_dlSelfReduceRetryAdversary
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {k : ℕ → ℕ} {n : ℕ} {d : F.Desc}
    {u : F.Carrier d} {out : List Bool}
    (hout : out ∈ (ProbComp.eval
      (F.dlSelfReduceRetryAdversary adversary k n (d, F.encode d u))).support) :
    out = [] ∨ (ofBits out : ZMod (F.order d)) • F.generator d = u :=
  (F.eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary hout).imp_right
    fun h => F.encode_injective d h

/-- On a word that encodes no element of the group `d`, the loop outputs the empty word. -/
theorem eq_nil_of_mem_support_dlSelfReduceRetryAdversary_of_not_mem_range
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {k : ℕ → ℕ} {n : ℕ} {d : F.Desc}
    {w out : List Bool} (hw : w ∉ Set.range (F.encode d))
    (hout : out ∈ (ProbComp.eval (F.dlSelfReduceRetryAdversary adversary k n (d, w))).support) :
    out = [] :=
  (F.eq_nil_or_encode_smul_eq_of_mem_support_dlSelfReduceRetryAdversary hout).resolve_right
    fun h => hw ⟨_, h⟩

/-- One checked attempt on `α • g` fails its test with probability at most `1 - (ε - 1 / 2 ^ n)`:
it passes exactly when the masked call returns `α`. -/
private theorem toOuterMeasure_eval_dlSelfReduceAttempt_not_le
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    (ProbComp.eval (F.dlSelfReduceAttempt adversary n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure {p | ¬ (p.1 = true)} ≤
      1 - ((dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) -
        1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) := by
  refine Probability.PMF.toOuterMeasure_compl_le_one_sub _ {p : Bool × List Bool | p.1 = true} ?_
  have hpass : (ProbComp.eval (F.dlSelfReduceAttempt adversary n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure {p | p.1 = true} =
      ProbComp.eval ((fun x => decide (x = α)) <$>
        F.discreteLogAdversary (F.dlSelfReduceAdversary adversary) n d (α • F.generator d))
        true := by
    rw [← PMF.toOuterMeasure_apply_singleton]
    simp only [dlSelfReduceAttempt, discreteLogAdversary, ProbComp.eval_map, PMF.map_comp,
      PMF.toOuterMeasure_map_apply]
    congr 1
    ext out
    simp [F.smul_encode, (F.encode_injective d).eq_iff, (F.smul_generator_injective d).eq_iff]
  rw [hpass]
  have h := F.advantage_dlSelfReduceAdversary_le adversary n d α
  rw [Experiment.advantage, Game.advantage, NNReal.nndist_eq] at h
  have h' := tsub_le_iff_right.mpr (tsub_le_iff_left.mp ((le_max_right _ _).trans h))
  exact (ENNReal.coe_le_coe.mpr h').trans_eq (Game.coe_succProbability_ennreal _)

/-- The discrete-logarithm game reads an answer as `α` at least as often as the answer is nonempty
and reads as `α`. -/
private theorem toOuterMeasure_le_eval_discreteLogAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (u : F.Carrier d) (α : ZMod (F.order d)) :
    (ProbComp.eval (adversary n (d, F.encode d u))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} ≤
      ProbComp.eval (F.discreteLogAdversary adversary n d u) α := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  simp only [discreteLogAdversary, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  exact PMF.toOuterMeasure_mono _ fun out h => h.1.2

/-- The discrete-logarithm game reads an answer as an exponent other than `α` at most as often as
the answer is empty or reads as an exponent other than `α`. -/
private theorem toOuterMeasure_eval_discreteLogAdversary_ne_le
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (u : F.Carrier d) (α : ZMod (F.order d)) :
    (ProbComp.eval (F.discreteLogAdversary adversary n d u)).toOuterMeasure {x | x ≠ α} ≤
      (ProbComp.eval (adversary n (d, F.encode d u))).toOuterMeasure
        {out | out = [] ∨ (ofBits out : ZMod (F.order d)) ≠ α} := by
  simp only [discreteLogAdversary, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
  exact PMF.toOuterMeasure_mono _ fun out h => Or.inr h.1

/-- **The loop on every instance**: on the encoding of `α • g`, `k n` checked attempts return a
nonempty word that reads as `α` with probability at least `1 - (1 - (ε - 1 / 2 ^ n)) ^ k n`, where
`ε` is the adversary's success in the group `d`. The iteration remark after [BonehShoup2023],
Theorem 10.2 (p. 412) gives `1 - (1 - ε) ^ k` without the sampling loss. The event excludes the
empty word, the book's `fail`, for the reason given at
`le_toOuterMeasure_dlSelfReduceRetryAdversary_one`. -/
theorem one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (k : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    1 - (1 - ((dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) -
        1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) ^ k n ≤
      (ProbComp.eval (F.dlSelfReduceRetryAdversary adversary k n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} := by
  let μ := ProbComp.eval (OracleComp.retry (fun p : Bool × List Bool => p.1)
    (F.dlSelfReduceAttempt adversary n (d, F.encode d (α • F.generator d))) (k n))
  have hnone : μ none ≤ (1 - ((dlAdvantage (F.order d) (F.generator d)
      (F.discreteLogAdversary adversary n d) - 1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) ^ k n :=
    OracleComp.evalWith_retry_none_le _ _ _
      (F.toOuterMeasure_eval_dlSelfReduceAttempt_not_le adversary n d α) (k n)
  have hsome : μ.toOuterMeasure {none}ᶜ ≤
      (ProbComp.eval (F.dlSelfReduceRetryAdversary adversary k n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} := by
    simp only [dlSelfReduceRetryAdversary, ProbComp.eval_map, PMF.toOuterMeasure_map_apply]
    refine PMF.toOuterMeasure_mono _ ?_
    rintro (_ | ⟨b, out⟩) ⟨ho, hsupp⟩
    · exact absurd rfl ho
    · obtain ⟨hne, henc⟩ := F.ne_nil_and_encode_smul_eq_of_mem_support_retry hsupp
      exact (show out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α from
        ⟨hne, F.smul_generator_injective d (F.encode_injective d henc)⟩)
  have hsum := Probability.PMF.toOuterMeasure_add_compl_ennreal μ {none}
  rw [PMF.toOuterMeasure_apply_singleton] at hsum
  calc _ ≤ 1 - μ none := tsub_le_tsub_left hnone 1
    _ = μ.toOuterMeasure {none}ᶜ :=
        (ENNReal.eq_sub_of_add_eq (PMF.apply_ne_top _ _) (by rw [add_comm]; exact hsum)).symm
    _ ≤ _ := hsome

/-- **[BonehShoup2023], Theorem 10.2, with the sampling loss**: on the encoding of every instance
`α • g`, one checked attempt returns a nonempty word that reads as `α` with probability at least
`ε - 1 / 2 ^ n`, where `ε` is the adversary's success in the group `d`.

The bound is on the output word, not on the exponent that the discrete-logarithm game reads from
it. The game reads the empty word, the book's `fail`, as `0`, so on the instance `α = 0` the
game-level bound `le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one` holds even for a
loop that always fails. Excluding the empty word gives the book's claim that `B` returns an answer
other than `fail`, the discrete logarithm, with probability `ε`, for every `u`.

The book's equality `= ε` is `Cslib.Crypto.eval_dlSelfReduce_one_smul_some` for the fixed-group
program with a uniform mask; here the mask is drawn by `sampleExp`, and only the lower bound is
stated. The attempt is efficient (`isPPTOn_dlSelfReduceRetryAdversary`). -/
theorem le_toOuterMeasure_dlSelfReduceRetryAdversary_one
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    ((dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) -
        1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤
      (ProbComp.eval (F.dlSelfReduceRetryAdversary adversary (fun _ => 1) n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α} := by
  have h := F.one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary adversary (fun _ => 1) n d α
  rwa [pow_one, ENNReal.sub_sub_cancel ENNReal.one_ne_top
    (by exact_mod_cast tsub_le_self.trans (Game.succProbability_le_one _))] at h

/-- The bound of `one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary` for the exponent that
the discrete-logarithm game reads from the loop's answer. At `α = 0` it holds for every loop, since
the game reads the empty word as `0`. -/
theorem one_sub_pow_le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (k : ℕ → ℕ) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    1 - (1 - ((dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) -
        1 / 2 ^ n : ℝ≥0) : ℝ≥0∞)) ^ k n ≤
      ProbComp.eval (F.discreteLogAdversary (F.dlSelfReduceRetryAdversary adversary k) n d
        (α • F.generator d)) α :=
  (F.one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary adversary k n d α).trans
    (F.toOuterMeasure_le_eval_discreteLogAdversary _ n d _ α)

/-- The bound of `le_toOuterMeasure_dlSelfReduceRetryAdversary_one` for the exponent that the
discrete-logarithm game reads from the loop's answer. At `α = 0` it holds for every loop, since
the game reads the empty word as `0`. -/
theorem le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (n : ℕ) (d : F.Desc)
    (α : ZMod (F.order d)) :
    ((dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d) -
        1 / 2 ^ n : ℝ≥0) : ℝ≥0∞) ≤
      ProbComp.eval (F.discreteLogAdversary (F.dlSelfReduceRetryAdversary adversary fun _ => 1)
        n d (α • F.generator d)) α :=
  (F.le_toOuterMeasure_dlSelfReduceRetryAdversary_one adversary n d α).trans
    (F.toOuterMeasure_le_eval_discreteLogAdversary _ n d _ α)

/-- **The iteration remark after [BonehShoup2023], Theorem 10.2** (p. 412), in a fixed group with
the sampling loss: if the adversary wins the discrete-logarithm game in the group `d` with
probability at least `1 / invEps n` and `1 / 2 ^ n ≤ 1 / (2 * invEps n)`, then on the encoding of
every instance `α • g` the loop with `n * (2 * invEps n)` attempts errs, that is returns the empty
word or a word that does not read as `α`, with probability at most `(1 / 2) ^ n`.
The book runs `n ⌈1 / ε⌉` attempts and bounds the error by `exp (-n)`. The second hypothesis forces
`0 < invEps n`. -/
theorem dlSelfReduceRetryAdversary_error_le_pow
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (invEps : ℕ → ℕ) (n : ℕ)
    (d : F.Desc) (α : ZMod (F.order d))
    (hadv : 1 / (invEps n : ℝ) ≤
      Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) adversary n))
    (hmod : 1 / (2 ^ n : ℝ) ≤ 1 / (2 * (invEps n : ℝ))) :
    ((ProbComp.eval (F.dlSelfReduceRetryAdversary adversary (fun n => n * (2 * invEps n)) n
        (d, F.encode d (α • F.generator d)))).toOuterMeasure
        {out | out = [] ∨ (ofBits out : ZMod (F.order d)) ≠ α}).toReal ≤ (1 / 2 : ℝ) ^ n := by
  have hmpos : (0 : ℝ) < invEps n := by
    by_contra h
    have h0 : (invEps n : ℝ) = 0 := le_antisymm (not_lt.mp h) (Nat.cast_nonneg _)
    rw [h0, mul_zero, div_zero] at hmod
    exact absurd hmod (not_le.mpr (by positivity))
  rw [F.succProbability_discreteLogGame_pure] at hadv
  set ε := dlAdvantage (F.order d) (F.generator d) (F.discreteLogAdversary adversary n d)
  set c : ℝ≥0 := ε - 1 / 2 ^ n with hc
  have hc1 : c ≤ 1 := tsub_le_self.trans (Game.succProbability_le_one _)
  have hcge : 1 / (2 * (invEps n : ℝ)) ≤ (c : ℝ) := by
    have hsub : (ε : ℝ) - 1 / 2 ^ n ≤ (c : ℝ) := by
      simp only [c, NNReal.coe_sub_def, NNReal.coe_div, NNReal.coe_one, NNReal.coe_pow,
        NNReal.coe_ofNat]
      exact le_max_left _ _
    have hhalf : 1 / (invEps n : ℝ) - 1 / (2 * (invEps n : ℝ)) = 1 / (2 * (invEps n : ℝ)) := by
      field_simp
      ring
    linarith
  have hmain := F.one_sub_pow_le_toOuterMeasure_dlSelfReduceRetryAdversary adversary
    (fun n => n * (2 * invEps n)) n d α
  have herr := Probability.PMF.toOuterMeasure_compl_le_one_sub _ _ hmain
  have hpow1 : (1 - (c : ℝ≥0∞)) ^ (n * (2 * invEps n)) ≤ 1 :=
    pow_le_one₀ (by positivity) tsub_le_self
  rw [ENNReal.sub_sub_cancel ENNReal.one_ne_top hpow1] at herr
  have hset : {out : List Bool | out = [] ∨ (ofBits out : ZMod (F.order d)) ≠ α} =
      {out | out ≠ [] ∧ (ofBits out : ZMod (F.order d)) = α}ᶜ := by
    ext out
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_and_or, not_not, ne_eq]
  rw [hset]
  calc _ ≤ ((1 - (c : ℝ≥0∞)) ^ (n * (2 * invEps n))).toReal :=
        ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top hpow1) herr
    _ = (1 - (c : ℝ)) ^ (n * (2 * invEps n)) := by
        rw [ENNReal.toReal_pow, ENNReal.toReal_sub_of_le (by exact_mod_cast hc1)
          ENNReal.one_ne_top, ENNReal.toReal_one, ENNReal.coe_toReal]
    _ ≤ (1 - 1 / (2 * (invEps n : ℝ))) ^ (n * (2 * invEps n)) :=
        pow_le_pow_left₀ (sub_nonneg.mpr (by exact_mod_cast hc1)) (by linarith) _
    _ ≤ Real.exp (-(n : ℝ)) := by
        refine Real.one_sub_pow_le_exp ?_ ?_
        · rw [div_le_one (by positivity)]
          have : (1 : ℝ) ≤ invEps n := by
            exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hmpos.ne')
          linarith
        · push_cast
          field_simp
          exact le_rfl
    _ ≤ (1 / 2 : ℝ) ^ n := Real.exp_le_half_pow n le_rfl

/-- The bound of `dlSelfReduceRetryAdversary_error_le_pow` for the exponent that the
discrete-logarithm game reads from the loop's answer: it reads an exponent other than `α` with
probability at most `(1 / 2) ^ n`. -/
theorem discreteLogAdversary_dlSelfReduceRetryAdversary_error_le_pow
    (adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)) (invEps : ℕ → ℕ) (n : ℕ)
    (d : F.Desc) (α : ZMod (F.order d))
    (hadv : 1 / (invEps n : ℝ) ≤
      Game.succProbability (F.discreteLogGame (fun _ => PMF.pure d) adversary n))
    (hmod : 1 / (2 ^ n : ℝ) ≤ 1 / (2 * (invEps n : ℝ))) :
    ((ProbComp.eval (F.discreteLogAdversary
        (F.dlSelfReduceRetryAdversary adversary fun n => n * (2 * invEps n)) n d
        (α • F.generator d))).toOuterMeasure {x | x ≠ α}).toReal ≤ (1 / 2 : ℝ) ^ n :=
  (ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
    (F.toOuterMeasure_eval_discreteLogAdversary_ne_le _ n d _ α)).trans
    (F.dlSelfReduceRetryAdversary_error_le_pow adversary invEps n d α hadv hmod)

/-- **Discrete logarithm on every instance with negligible error**: if `invEps` is computable in
polynomial time in unary and, for large `n`, `0 < invEps n` and the adversary wins the
discrete-logarithm game in the group `d n` with probability at least `1 / invEps n`, then on the
encoding of every sequence of instances `α n • g` in `d n` the loop with `n * (2 * invEps n)`
attempts errs, that is returns the empty word or a word that does not read as `α n`, with
negligible probability.
The loop is uniform strict PPT (`isPPTOn_dlSelfReduceRetryAdversary_invEps`). This is the
conclusion of the remark after [BonehShoup2023], Theorem 10.2 (p. 412), "if `1/ε` is
poly-bounded, we can efficiently compute the discrete logarithm of any group element with
negligible failure probability", with `invEps` in place of `⌈1 / ε⌉`. -/
theorem negligible_dlSelfReduceRetryAdversary_error
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {invEps : ℕ → ℕ}
    (hinvEps : ComputableInPolyTime invEps encUnary encUnary)
    (d : ℕ → F.Desc) (α : ∀ n, ZMod (F.order (d n)))
    (hpos : ∀ᶠ n in Filter.atTop, 0 < invEps n)
    (hadv : ∀ᶠ n in Filter.atTop, 1 / (invEps n : ℝ) ≤
      Game.succProbability (F.discreteLogGame (fun _ => PMF.pure (d n)) adversary n)) :
    Negligible fun n =>
      ((ProbComp.eval (F.dlSelfReduceRetryAdversary adversary (fun n => n * (2 * invEps n)) n
        (d n, F.encode (d n) (α n • F.generator (d n))))).toOuterMeasure
        {out | out = [] ∨ (ofBits out : ZMod (F.order (d n))) ≠ α n}).toNNReal := by
  have hgeom : Negligible fun n => ((2⁻¹ : ℝ≥0) ^ n) := by negligible
  have hpoly : PolynomiallyBounded fun n => 2 * invEps n + 1 :=
    ((PolynomiallyBounded.const 2).mul hinvEps.tidy.polynomiallyBounded).add (.const 1)
  have hmod : ∀ᶠ n in Filter.atTop, 1 / (2 ^ n : ℝ) ≤ 1 / (2 * (invEps n : ℝ)) := by
    filter_upwards [hpos, hgeom.eventually_le_inv_polynomial hpoly (fun _ => Nat.succ_pos _)]
      with n hn hlt
    have hmpos : (0 : ℝ) < invEps n := by exact_mod_cast hn
    refine le_trans ?_
      (one_div_le_one_div_of_le (by positivity) (le_add_of_nonneg_right zero_le_one))
    simpa only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat, inv_pow, one_div,
      Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one] using hlt
  negligible eventually (by
    filter_upwards [hadv, hmod] with n hadv_n hmod_n
    exact F.dlSelfReduceRetryAdversary_error_le_pow adversary invEps n (d n) (α n) hadv_n hmod_n)

/-- The conclusion of `negligible_dlSelfReduceRetryAdversary_error` for the exponent that the
discrete-logarithm game reads from the loop's answer: it reads an exponent other than `α n` with
negligible probability. -/
theorem negligible_discreteLogAdversary_dlSelfReduceRetryAdversary_error
    {adversary : ℕ → F.Desc × List Bool → ProbComp (List Bool)} {invEps : ℕ → ℕ}
    (hinvEps : ComputableInPolyTime invEps encUnary encUnary)
    (d : ℕ → F.Desc) (α : ∀ n, ZMod (F.order (d n)))
    (hpos : ∀ᶠ n in Filter.atTop, 0 < invEps n)
    (hadv : ∀ᶠ n in Filter.atTop, 1 / (invEps n : ℝ) ≤
      Game.succProbability (F.discreteLogGame (fun _ => PMF.pure (d n)) adversary n)) :
    Negligible fun n =>
      ((ProbComp.eval (F.discreteLogAdversary
        (F.dlSelfReduceRetryAdversary adversary fun n => n * (2 * invEps n)) n (d n)
        (α n • F.generator (d n)))).toOuterMeasure {x | x ≠ α n}).toNNReal :=
  negligible_of_le (F.negligible_dlSelfReduceRetryAdversary_error hinvEps d α hpos hadv) fun n =>
    ENNReal.toNNReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
      (F.toOuterMeasure_eval_discreteLogAdversary_ne_le _ n (d n) _ (α n))

/-! ### Computational Diffie–Hellman -/

/-- **[BonehShoup2023], Exercise 10.6, with the sampling loss**: on every pair `(α • g, β • g)`,
`cdhSelfReduceAdversary` returns `(α * β) • g` with the probability with which the adversary wins
the CDH experiment in the group `d`, up to `2 / 2 ^ n`, the loss of the two `sampleExp` masks. The
exercise asks for equality; with uniform masks it holds
(`Cslib.Crypto.eval_cdhSelfReduce_smul_apply`). The reduction is efficient
(`isPPT_cdhSelfReduceAdversary`). -/
theorem advantage_cdhSelfReduceAdversary_le (adversary : F.CDHAdversary) (n : ℕ) (d : F.Desc)
    (α β : ZMod (F.order d)) :
    Experiment.advantage
      ((fun w => decide (w = (α * β) • F.generator d)) <$>
        F.cdhSelfReduceAdversary adversary n d (α • F.generator d) (β • F.generator d))
      (cdhExperiment (F.order d) (F.generator d) (adversary n d)) ≤ 2 / 2 ^ n := by
  let k : ZMod (F.order d) → ZMod (F.order d) → Game := fun ρ τ =>
    (ProbComp.eval (adversary n d (α • F.generator d + ρ • F.generator d)
      (β • F.generator d + τ • F.generator d))).map fun w =>
        decide (w - τ • α • F.generator d - ρ • β • F.generator d - (ρ * τ) • F.generator d =
          (α * β) • F.generator d)
  have h1 : ProbComp.eval ((fun w => decide (w = (α * β) • F.generator d)) <$>
        F.cdhSelfReduceAdversary adversary n d (α • F.generator d) (β • F.generator d)) =
      (ProbComp.eval (F.sampleExp n d)).bind fun r =>
        (ProbComp.eval (F.sampleExp n d)).bind fun t =>
          k (r : ZMod (F.order d)) (t : ZMod (F.order d)) := by
    simp [cdhSelfReduceAdversary, k]
  have h2 : ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun ρ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ => k ρ τ) =
      (ProbComp.eval (cdhSelfReduce (F.order d) (F.generator d) (adversary n d)
        (α • F.generator d) (β • F.generator d))).map
        fun w => decide (w = (α * β) • F.generator d) := by
    simp [k, cdhSelfReduce, PMF.map_bind, PMF.map_comp, Function.comp_def]
  have h3 : Game.succProbability ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun ρ =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun τ => k ρ τ) =
      Game.succProbability (ProbComp.eval
        (cdhExperiment (F.order d) (F.generator d) (adversary n d))) := by
    rw [h2, Game.succProbability, Probability.PMF.map_decide_eq_apply_true,
      eval_cdhSelfReduce_smul_apply]
  have h := F.advantage_bind_sampleExp_pair_le n d k
  rw [Experiment.advantage, h1]
  rwa [Game.advantage, h3] at h

/-- `cdhSelfReduceAdversary` wins the worst-case game on the pairs `(α d • g, β d • g)` within
`2 / 2 ^ n` of the adversary's success in the average-case CDH game, for every setup law. -/
theorem advantage_cdhWorstCaseGame_cdhGame_le (setup : ℕ → PMF F.Desc)
    (α β : ∀ d : F.Desc, ZMod (F.order d)) (adversary : F.CDHAdversary) (n : ℕ) :
    Game.advantage (F.cdhWorstCaseGame setup α β (F.cdhSelfReduceAdversary adversary) n)
      (F.cdhGame setup adversary n) ≤ 2 / 2 ^ n :=
  Game.advantage_withSetup_le _ _ _ fun d _ =>
    F.advantage_cdhSelfReduceAdversary_le adversary n d (α d) (β d)

/-- The adversary's average-case CDH success is at most the reduction's worst-case success plus
`2 / 2 ^ n`. -/
theorem succProbability_cdhGame_le_cdhWorstCaseGame (setup : ℕ → PMF F.Desc)
    (α β : ∀ d : F.Desc, ZMod (F.order d)) (adversary : F.CDHAdversary) (n : ℕ) :
    Game.succProbability (F.cdhGame setup adversary n) ≤
      Game.succProbability (F.cdhWorstCaseGame setup α β (F.cdhSelfReduceAdversary adversary) n) +
        2 / 2 ^ n := by
  refine Game.succProbability_le_add_of_advantage_le ?_
  rw [Game.advantage_comm]
  exact F.advantage_cdhWorstCaseGame_cdhGame_le setup α β adversary n

/-- Average-case CDH hardness from worst-case hardness: if for every uniform strict PPT CDH
adversary there are pairs `(α d • g, β d • g)` on which it wins the worst-case game with negligible
probability, then `CDH` holds for the setup law. The pairs may depend on the adversary. This
formulation and `cdhWorstCaseGame` are this library's. The premise of
`Cslib.Crypto.PrimeOrderGroupFamily.ddh_of_worstCase` is stronger: it fixes the instances before
the distinguisher. -/
theorem cdh_of_worstCase {setup : ℕ → PMF F.Desc}
    (hworst : ∀ adversary : F.CDHAdversary, adversary.IsPPT →
      ∃ α β : ∀ d : F.Desc, ZMod (F.order d),
        Negligible fun n => Game.succProbability (F.cdhWorstCaseGame setup α β adversary n)) :
    F.CDH setup := by
  intro adversary hA
  obtain ⟨α, β, hw⟩ := hworst _ (F.isPPT_cdhSelfReduceAdversary hA)
  negligible using F.succProbability_cdhGame_le_cdhWorstCaseGame setup α β adversary

end Cslib.Crypto.PrimeOrderGroupFamily
