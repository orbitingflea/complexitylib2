/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Computational.Encryption.Hybrid
public import CslibFrontier.Crypto.Computational.Encryption.PolyTime
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.PPT
import Mathlib.Data.Fintype.Pi

/-!
# Message-recovery security from semantic security (Boneh–Shoup §2.2.3)

A semantically secure cipher is secure against message recovery ([BonehShoup2023], Section 2.2.3,
Attack Game 2.2, p. 18; Definition 2.3 and Theorem 2.7, p. 19). We formalize both the concrete
exact advantage identity for a typed symmetric cipher `Cipher K M C` and the asymptotic word-level
statement over `{0, 1}^{msgLen n}` against `DEMOneTimeKeyWordINDCPA` together with its uniform
strict PPT certificate.

Relative to [BonehShoup2023], §2.2.3, pp. 18–19, this formalization makes two hypotheses explicit:
* On a concrete `Cipher K M C`, `messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction`
  requires `hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true` so `Cipher.oneTimeExperiment` admits every
  pair sampled independently from the finite nonempty type `M` by `messageRecoveryReduction`.
  (Theorem 2.7 as printed has no such hypothesis. It is needed here because Attack Game 2.1
  admits only pairs of equal length, and the reduction submits two independent uniform messages.)
* On word messages `{0, 1}^{msgLen n}`, an adversary `A : ℕ → List Bool → ProbComp (List Bool)` can
  output lists of arbitrary length, whereas Attack Game 2.2 requires `mHat ∈ M`.
  `messageRecoveryWordAdvantage_eq_demKeyGameOn` and
  `DEMOneTimeKeyWordINDCPA.negligible_messageRecoveryWordAdvantage` therefore require
  `hA_len : ∀ n ct mHat, mHat ∈ (ProbComp.eval (A n ct)).support → mHat.length = msgLen n`, plus
  `ComputableInPolyTime msgLen encUnary encUnary` for PPT message sampling. Checked counterexamples
  in `CslibFrontierTests.Crypto.MessageRecovery` show that `hvalid` and `hA_len` are needed.

## Main definitions

* `Cslib.Crypto.Encryption.messageRecoveryExperiment`: Attack Game 2.2 for `Cipher K M C`.
* `Cslib.Crypto.Encryption.messageRecoveryAdvantage`: `MRadv[A, E] := |Pr[W] - 1 / |M||`.
* `Cslib.Crypto.Encryption.messageRecoveryReduction`: explicit `TwoStage` semantic-security
  reduction `B` from a message-recovery adversary `A`.
* `Cslib.Crypto.Encryption.messageRecoveryWordExperiment`,
  `Cslib.Crypto.Encryption.messageRecoveryWordAdvantage`,
  `Cslib.Crypto.Encryption.messageRecoveryWordToDEMAdversary`: word-level Attack Game 2.2,
  advantage over `{0, 1}^{msgLen n}`, and explicit `WordAdversary` reduction.

## Main results

* `Cslib.Crypto.Encryption.messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction`: exact
  equality `MRadv[A, E] = SSadv[messageRecoveryReduction (ProbComp.uniform M) A, E]`
  (Theorem 2.7; inequality (2.5) is its `.le`).
* `Cslib.Crypto.Encryption.isPPT_messageRecoveryWordToDEMAdversary`: uniform strict PPT
  certificate `AdversaryOf.IsPPT encBits (messageRecoveryWordToDEMAdversary msgLen A)`.
* `Cslib.Crypto.Encryption.messageRecoveryWordAdvantage_eq_demKeyGameOn`: exact word-level
  advantage equality derived from the concrete identity.
* `Cslib.Crypto.Encryption.DEMOneTimeKeyWordINDCPA.negligible_messageRecoveryWordAdvantage`:
  asymptotic Theorem 2.7 for `DEMOneTimeKeyWordINDCPA`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 2.2.3 (Attack Game 2.2, p. 18; Definition 2.3 and
  Theorem 2.7, p. 19).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

section MessageRecoveryConcrete

variable {K M C : Type}

/-- Message-recovery attack game ([BonehShoup2023], Attack Game 2.2, p. 18): sample a uniform
message `m` from `M` and key `k ← sampleKey`, encrypt `c ← E.encrypt k m`, run `A c`, and win iff
`mHat == m`. -/
@[expose] noncomputable def messageRecoveryExperiment (E : Cipher K M C)
    [Fintype M] [Nonempty M] [DecidableEq M]
    (sampleKey : ProbComp K) (A : C → ProbComp M) : Experiment := do
  let m ← ProbComp.uniform M
  let k ← sampleKey
  let c ← E.encrypt k m
  let mHat ← A c
  return (mHat == m)

/-- Message-recovery advantage `MRadv[A, E] := |Pr[W] - 1 / |M||` ([BonehShoup2023], Attack
Game 2.2, p. 18). -/
@[expose] noncomputable def messageRecoveryAdvantage (E : Cipher K M C)
    [Fintype M] [Nonempty M] [DecidableEq M]
    (sampleKey : ProbComp K) (A : C → ProbComp M) : ℝ≥0 :=
  nndist (Game.succProbability (ProbComp.eval (messageRecoveryExperiment E sampleKey A)))
    ((Fintype.card M : ℝ≥0)⁻¹)

/-- Explicit semantic-security reduction `B` from a message-recovery adversary `A` given a
message sampler `sampleMsg` ([BonehShoup2023], Theorem 2.7, p. 19): sample independent
`m₀, m₁ ← sampleMsg`, submit `(m₀, m₁)`, run `mHat ← A c` on the challenge ciphertext, and
output `mHat == m₁`. Concrete finite theorems instantiate `sampleMsg := ProbComp.uniform M`;
word-level reductions instantiate `sampleMsg := BitString.sampleList (msgLen n)`. -/
@[expose] noncomputable def messageRecoveryReduction [BEq M]
    (sampleMsg : ProbComp M) (A : C → ProbComp M) : TwoStage Unit (MessagePair M) C Bool M where
  choose _ := do
    let m₀ ← sampleMsg
    let m₁ ← sampleMsg
    return (⟨m₀, m₁⟩, m₁)
  guess m₁ c := do
    let mHat ← A c
    return (mHat == m₁)

private theorem eval_oneTimeExperiment_messageRecoveryReduction_true (E : Cipher K M C)
    [Fintype M] [Nonempty M] [DecidableEq M] (sampleKey : ProbComp K) {valid : M → M → Bool}
    (hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true) (A : C → ProbComp M) :
    ProbComp.eval (E.oneTimeExperiment sampleKey valid
        (messageRecoveryReduction (ProbComp.uniform M) A) true) =
      ProbComp.eval (messageRecoveryExperiment E sampleKey A) := by
  simp only [Cipher.oneTimeExperiment, messageRecoveryReduction, messageRecoveryExperiment,
    lrExperiment, MessagePair.select_true, hvalid, ↓reduceIte, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  pmf_swap with m₀
  simp only [PMF.bind_const]

private theorem succProbability_oneTimeExperiment_messageRecoveryReduction_false
    (E : Cipher K M C) [Fintype M] [Nonempty M] [DecidableEq M] (sampleKey : ProbComp K)
    {valid : M → M → Bool} (hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true) (A : C → ProbComp M) :
    Game.succProbability (ProbComp.eval
      (E.oneTimeExperiment sampleKey valid
        (messageRecoveryReduction (ProbComp.uniform M) A) false)) =
      (Fintype.card M : ℝ≥0)⁻¹ := by
  have htrue :
      ProbComp.eval (E.oneTimeExperiment sampleKey valid
          (messageRecoveryReduction (ProbComp.uniform M) A) false) true =
        ((Fintype.card M : ℝ≥0∞)⁻¹) := by
    have hrewrite :
        ProbComp.eval (E.oneTimeExperiment sampleKey valid
            (messageRecoveryReduction (ProbComp.uniform M) A) false) =
          ((ProbComp.eval sampleKey).bind fun k =>
            (PMF.uniformOfFintype M).bind fun m₀ =>
            (ProbComp.eval (E.encrypt k m₀)).bind fun c =>
            (ProbComp.eval (A c)).bind fun mHat =>
            (PMF.uniformOfFintype M).map fun m₁ => (mHat == m₁)) := by
      simp only [Cipher.oneTimeExperiment, messageRecoveryReduction, lrExperiment,
        MessagePair.select_false, hvalid, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
      pmf_swap
    rw [hrewrite]
    apply Probability.PMF.bind_apply_of_forall; intro k
    apply Probability.PMF.bind_apply_of_forall; intro m₀
    apply Probability.PMF.bind_apply_of_forall; intro c
    apply Probability.PMF.bind_apply_of_forall; intro mHat
    exact Probability.PMF.uniformOfFintype_bind_decide_eq_apply_true mHat
  apply NNReal.coe_injective
  rw [Game.coe_succProbability, htrue, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    NNReal.coe_inv, NNReal.coe_natCast]

/-- **Concrete advantage equality for Theorem 2.7** ([BonehShoup2023], p. 19):
`MRadv[A, E] = SSadv[messageRecoveryReduction (ProbComp.uniform M) A, E]` whenever `valid` admits
every message pair in `M`. Display (2.5), `MRadv[A, E] ≤ SSadv[B, E]`, is the `.le` projection of
this equality. -/
theorem messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction (E : Cipher K M C)
    [Fintype M] [Nonempty M] [DecidableEq M] (sampleKey : ProbComp K) {valid : M → M → Bool}
    (hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true) (A : C → ProbComp M) :
    messageRecoveryAdvantage E sampleKey A =
      Experiment.advantage
        (E.oneTimeExperiment sampleKey valid
          (messageRecoveryReduction (ProbComp.uniform M) A) false)
        (E.oneTimeExperiment sampleKey valid
          (messageRecoveryReduction (ProbComp.uniform M) A) true) := by
  rw [messageRecoveryAdvantage, Experiment.advantage, Game.advantage, nndist_comm,
    eval_oneTimeExperiment_messageRecoveryReduction_true E sampleKey hvalid A,
    succProbability_oneTimeExperiment_messageRecoveryReduction_false E sampleKey hvalid A]

end MessageRecoveryConcrete

section MessageRecoveryWord

/-- Word-level message-recovery experiment over `{0, 1}^{msgLen n}` with uniform `keyLen n`-bit
keys ([BonehShoup2023], Attack Game 2.2, p. 18). -/
@[expose] noncomputable def messageRecoveryWordExperiment (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : Experiment := do
  let m ← BitString.sampleList (msgLen n)
  let k ← BitString.sampleList (keyLen n)
  let c ← encryptSym n k m
  let mHat ← A n c
  return (mHat == m)

/-- Word-level message-recovery advantage `|Pr[W] - 1 / 2^(msgLen n)|`
([BonehShoup2023], Attack Game 2.2, p. 18). -/
@[expose] noncomputable def messageRecoveryWordAdvantage (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp (List Bool)) (n : ℕ) : ℝ≥0 :=
  nndist (Game.succProbability
    (ProbComp.eval (messageRecoveryWordExperiment msgLen keyLen encryptSym A n)))
    ((2 ^ msgLen n : ℝ≥0)⁻¹)

/-- Explicit `WordAdversary` reduction for message recovery on `{0, 1}^{msgLen n}`
([BonehShoup2023], Theorem 2.7, p. 19). -/
@[expose] noncomputable def messageRecoveryWordToDEMAdversary (msgLen : ℕ → ℕ)
    (A : ℕ → List Bool → ProbComp (List Bool)) : WordAdversary where
  choose n _ := do
    let out ← (messageRecoveryReduction (BitString.sampleList (msgLen n)) (A n)).choose ()
    return ((out.1.msg₀, out.1.msg₁), out.2)
  guess n := (messageRecoveryReduction (BitString.sampleList (msgLen n)) (A n)).guess

/-- `messageRecoveryWordToDEMAdversary msgLen A` is uniform strict PPT whenever `msgLen` is unary
polynomial-time computable and `A` is uniform strict PPT on framed `(n, ct)` inputs. -/
theorem isPPT_messageRecoveryWordToDEMAdversary {msgLen : ℕ → ℕ}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary encBits) encBits (fun ⟨n, ct⟩ => A n ct)) :
    AdversaryOf.IsPPT encBits (messageRecoveryWordToDEMAdversary msgLen A) := by
  refine ⟨?_, ?_⟩
  · dsimp only [messageRecoveryWordToDEMAdversary, messageRecoveryReduction]
    ppt
  · dsimp only [messageRecoveryWordToDEMAdversary, messageRecoveryReduction]
    ppt

/-- Exact word-level advantage equality for Theorem 2.7, derived from the concrete equality
`messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction` over `BitString (msgLen n)`. The
length hypothesis `hA_len` models Attack Game 2.2's requirement `mHat ∈ M`. -/
theorem messageRecoveryWordAdvantage_eq_demKeyGameOn (msgLen keyLen : ℕ → ℕ)
    (encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool))
    (A : ℕ → List Bool → ProbComp (List Bool))
    (hA_len : ∀ n ct mHat, mHat ∈ (ProbComp.eval (A n ct)).support → mHat.length = msgLen n)
    (n : ℕ) :
    messageRecoveryWordAdvantage msgLen keyLen encryptSym A n =
      Game.advantage
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) false n))
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) true n)) := by
  let E : Cipher (List Bool) (BitString (msgLen n)) (List Bool) :=
    ⟨fun k m => encryptSym n k (List.ofFn m), fun _ _ => pure (fun _ => false)⟩
  let sampleKey : ProbComp (List Bool) := BitString.sampleList (keyLen n)
  let A' : List Bool → ProbComp (BitString (msgLen n)) := fun c => do
    let mHat ← A n c
    return BitString.ofList (msgLen n) mHat
  have hdecode : ∀ c (m₁ : BitString (msgLen n)),
      (ProbComp.eval (A n c)).bind
          (fun mHat => PMF.pure (BitString.ofList (msgLen n) mHat == m₁)) =
        (ProbComp.eval (A n c)).bind (fun mHat => PMF.pure (mHat == List.ofFn m₁)) := by
    intro c m₁
    refine Probability.PMF.bind_congr_on_support _ _ _ fun mHat hmHat => ?_
    have hm := hA_len n c mHat hmHat
    congr 1
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact ⟨fun h => by rw [← h, BitString.ofFn_ofList hm],
      fun h => by rw [h, BitString.ofList_ofFn]⟩
  have hmr : ProbComp.eval (messageRecoveryExperiment E sampleKey A') =
      ProbComp.eval (messageRecoveryWordExperiment msgLen keyLen encryptSym A n) := by
    simp only [messageRecoveryExperiment, messageRecoveryWordExperiment, E, sampleKey, A',
      ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, BitString.eval_sampleList,
      BitString.uniformList, PMF.bind_map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
    congr 1; funext m; congr 1; funext k; congr 1; funext c
    exact hdecode c m
  have hcard : (Fintype.card (BitString (msgLen n)) : ℝ≥0) = 2 ^ msgLen n := by
    simp [BitString]
  have hgame : ∀ bit : Bool,
      ProbComp.eval (E.oneTimeExperiment sampleKey (fun _ _ => true)
        (messageRecoveryReduction (ProbComp.uniform (BitString (msgLen n))) A') bit) =
      ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) bit n) := by
    intro bit
    simp only [Cipher.oneTimeExperiment, messageRecoveryReduction, demKeyGameOn,
      messageRecoveryWordToDEMAdversary, lrExperiment, ChoiceOut.msg₀, ChoiceOut.msg₁,
      E, sampleKey, A', ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
      BitString.eval_sampleList, BitString.uniformList, PMF.bind_map, PMF.bind_bind,
      PMF.pure_bind, Function.comp_def, List.length_ofFn, beq_self_eq_true]
    congr 1; funext k; congr 1; funext m₀; congr 1; funext m₁
    cases bit <;> simp only [MessagePair.select_false, MessagePair.select_true,
      Bool.false_eq_true, ↓reduceIte]
    · congr 1; funext c; exact hdecode c m₁
    · congr 1; funext c; exact hdecode c m₁
  have hconc := messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction
    E sampleKey (fun _ _ => rfl) A'
  rw [messageRecoveryAdvantage, hmr, hcard] at hconc
  rw [messageRecoveryWordAdvantage, hconc, Experiment.advantage, hgame false, hgame true]

/-- **Theorem 2.7 (asymptotic word-level statement)** ([BonehShoup2023], Theorem 2.7, p. 19):
if `encryptSym` is one-time key IND-CPA secure (`DEMOneTimeKeyWordINDCPA`), `msgLen` is unary
polynomial-time computable, and `A` is uniform strict PPT outputting words of length `msgLen n`
(modeling Attack Game 2.2's `mHat ∈ M`), then `A` has negligible message-recovery advantage. -/
theorem DEMOneTimeKeyWordINDCPA.negligible_messageRecoveryWordAdvantage {msgLen keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hsec : DEMOneTimeKeyWordINDCPA keyLen encryptSym)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    {A : ℕ → List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary encBits) encBits (fun ⟨n, ct⟩ => A n ct))
    (hA_len : ∀ n ct mHat, mHat ∈ (ProbComp.eval (A n ct)).support → mHat.length = msgLen n) :
    Negligible (messageRecoveryWordAdvantage msgLen keyLen encryptSym A) := by
  have hB : Negligible fun n =>
      Game.advantage
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) false n))
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) true n)) :=
    hsec _ (isPPT_messageRecoveryWordToDEMAdversary hmsgLen hA)
  exact hB.congr fun n =>
    (messageRecoveryWordAdvantage_eq_demKeyGameOn msgLen keyLen encryptSym A hA_len n).symm

end MessageRecoveryWord

end Cslib.Crypto.Encryption
