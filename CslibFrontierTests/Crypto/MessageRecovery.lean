/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Computational.Encryption.MessageRecovery
import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Tests for message-recovery security from semantic security

Checked clients and counterexamples for
`CslibFrontier.Crypto.Computational.Encryption.MessageRecovery`:
* Display (2.5) obtained as `.le` of
  `messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction`.
* A uniform word guesser is PPT and achieves negligible message-recovery advantage against any
  `DEMOneTimeKeyWordINDCPA` cipher.
* Counterexamples showing `hvalid` (concrete) and `hA_len` (word-level) are both necessary.
-/

namespace CslibFrontierTests.Crypto.MessageRecovery

open Cslib Cslib.Crypto Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

section ConcreteAndWordClients

/-- Boneh–Shoup display (2.5) is the `.le` projection of
`messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction`. -/
example {K M C : Type} (E : Cipher K M C) [Fintype M] [Nonempty M] [DecidableEq M]
    (sampleKey : ProbComp K) {valid : M → M → Bool}
    (hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true) (A : C → ProbComp M) :
    messageRecoveryAdvantage E sampleKey A ≤
      Experiment.advantage
        (E.oneTimeExperiment sampleKey valid
          (messageRecoveryReduction (ProbComp.uniform M) A) false)
        (E.oneTimeExperiment sampleKey valid
          (messageRecoveryReduction (ProbComp.uniform M) A) true) :=
  (messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction E sampleKey hvalid A).le

/-- Positive word-level client: uniformly guessing a `msgLen n`-bit string has negligible
message-recovery advantage against any `DEMOneTimeKeyWordINDCPA` cipher. -/
example {msgLen keyLen : ℕ → ℕ}
    {encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    (hsec : DEMOneTimeKeyWordINDCPA keyLen encryptSym)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary) :
    Negligible (messageRecoveryWordAdvantage msgLen keyLen encryptSym
      (fun n _ => BitString.sampleList (msgLen n))) := by
  refine hsec.negligible_messageRecoveryWordAdvantage hmsgLen ?_ ?_
  · refine IsPPTOn.preprocess isPPTOn_sampleList (hmsgLen.comp' (.fst _ _))
  · intro n _ mHat hmHat
    rw [BitString.eval_sampleList] at hmHat
    exact BitString.length_of_mem_support_uniformList hmHat

end ConcreteAndWordClients

section Counterexamples

/-- Shows `hvalid : ∀ m₀ m₁ : M, valid m₀ m₁ = true` is needed in
`messageRecoveryAdvantage_eq_advantage_messageRecoveryReduction`: a cipher revealing `m.isSome`
with `valid` checking equal option-length gives `MRadv = 1/3` while `SSadv = 0`. -/
theorem cex_messageRecovery_invalid_length :
    ∃ (M : Type) (_ : Fintype M) (_ : Nonempty M) (_ : DecidableEq M)
      (E : Cipher Unit M Bool) (sampleKey : ProbComp Unit) (valid : M → M → Bool)
      (A : Bool → ProbComp M),
      messageRecoveryAdvantage E sampleKey A = (1 : ℝ≥0) / 3 ∧
        Experiment.advantage
          (E.oneTimeExperiment sampleKey valid
            (messageRecoveryReduction (ProbComp.uniform M) A) false)
          (E.oneTimeExperiment sampleKey valid
            (messageRecoveryReduction (ProbComp.uniform M) A) true) = 0 := by
  let E : Cipher Unit (Option Bool) Bool :=
    ⟨fun _ m => pure m.isSome, fun _ _ => pure none⟩
  let A : Bool → ProbComp (Option Bool) := fun c => pure (if c then some false else none)
  refine ⟨Option Bool, inferInstance, inferInstance, inferInstance,
    E, pure (), fun m₀ m₁ => m₀.isSome == m₁.isSome, A, ?_, ?_⟩
  · have hsucc : Game.succProbability (ProbComp.eval (messageRecoveryExperiment E (pure ()) A)) =
        (2 : ℝ≥0) / 3 := by
      apply NNReal.coe_injective
      rw [Game.coe_succProbability]
      simp only [messageRecoveryExperiment, E, A, ProbComp.eval_bind, ProbComp.eval_pure,
        ProbComp.eval_uniform, PMF.pure_bind]
      rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
      · simp [PMF.uniformOfFintype_apply, Fintype.card_option, Fintype.card_bool]
        norm_num
      · intro a _; simp only [PMF.uniformOfFintype_apply, Fintype.card_option, Fintype.card_bool,
          Nat.reduceAdd, Nat.cast_ofNat, PMF.pure_apply, Bool.true_eq, beq_iff_eq, mul_ite,
          mul_one, mul_zero, ne_eq]
        repeat' split_ifs <;> norm_num
    rw [messageRecoveryAdvantage, hsucc]
    simp only [Fintype.card_option, Fintype.card_bool, Nat.reduceAdd, Nat.cast_ofNat]
    apply NNReal.coe_injective
    rw [coe_nndist, NNReal.dist_eq]
    norm_num [abs_of_pos]
  · rw [Experiment.advantage, Game.advantage, nndist_eq_zero]
    congr 1
    simp only [Cipher.oneTimeExperiment, E, A, messageRecoveryReduction, lrExperiment,
      MessagePair.select_false, MessagePair.select_true, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
    refine congrArg _ (funext fun m₀ => congrArg _ (funext fun m₁ => ?_))
    cases hm₀ : m₀.isSome <;> cases hm₁ : m₁.isSome <;> simp

/-- Shows `hA_len` is needed in `messageRecoveryWordAdvantage_eq_demKeyGameOn`: an adversary
outputting `[]` when `msgLen n = 1` achieves `messageRecoveryWordAdvantage = 1/2` while the
DEM advantage is `0`. -/
theorem cex_messageRecoveryWord_bad_length :
    let msgLen : ℕ → ℕ := fun _ => 1
    let keyLen : ℕ → ℕ := fun _ => 0
    let encryptSym : ℕ → List Bool → List Bool → ProbComp (List Bool) := fun _ _ _ => pure []
    let A : ℕ → List Bool → ProbComp (List Bool) := fun _ _ => pure []
    messageRecoveryWordAdvantage msgLen keyLen encryptSym A 0 = (1 : ℝ≥0) / 2 ∧
      Game.advantage
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) false 0))
        (ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
          keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) true 0)) = 0 := by
  intro msgLen keyLen encryptSym A
  constructor
  · have hfalse : ProbComp.eval (messageRecoveryWordExperiment msgLen keyLen encryptSym A 0) =
        PMF.pure false := by
      simp only [messageRecoveryWordExperiment, msgLen, keyLen, encryptSym, A, ProbComp.eval_bind,
        ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind]
      trans (BitString.uniformList 1).bind fun _ => PMF.pure false
      · refine Probability.PMF.bind_congr_on_support _ _ _ fun m hm => ?_
        have hlen : m.length = 1 := BitString.length_of_mem_support_uniformList hm
        have hne : ([] == m) = false := by
          simp only [beq_eq_false_iff_ne]
          intro heq
          have := congrArg List.length heq
          simp [hlen] at this
        simp [hne]
      · simp [PMF.bind_const]
    have hsucc : Game.succProbability (ProbComp.eval
        (messageRecoveryWordExperiment msgLen keyLen encryptSym A 0)) = 0 := by
      rw [hfalse]
      apply NNReal.coe_injective
      simp [Game.coe_succProbability]
    rw [messageRecoveryWordAdvantage, hsucc]
    apply NNReal.coe_injective
    rw [coe_nndist, NNReal.dist_eq]
    norm_num [msgLen, abs_of_neg]
  · have heq : ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) false 0) =
      ProbComp.eval (demKeyGameOn (fun _ _ m₀ m₁ => m₀.length == m₁.length)
        keyLen encryptSym (messageRecoveryWordToDEMAdversary msgLen A) true 0) := by
      simp only [demKeyGameOn, messageRecoveryWordToDEMAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁,
        Bool.false_eq_true, ↓reduceIte, encryptSym, A, ProbComp.eval_bind, ProbComp.eval_pure,
        BitString.eval_sampleList, PMF.bind_bind, PMF.pure_bind]
    rw [heq, Game.advantage_self]

/-- Dropping `hA_len` also falsifies the conclusion of
`DEMOneTimeKeyWordINDCPA.negligible_messageRecoveryWordAdvantage`: `A = fun _ _ => pure []`
against `otpKeyWordEncrypt keyLen` has constant message-recovery advantage `1/2` at every `n`. -/
theorem cex_messageRecoveryWord_not_negligible (keyLen : ℕ → ℕ) :
    let msgLen : ℕ → ℕ := fun _ => 1
    let A : ℕ → List Bool → ProbComp (List Bool) := fun _ _ => pure []
    DEMOneTimeKeyWordINDCPA keyLen (otpKeyWordEncrypt keyLen) ∧
      ComputableInPolyTime msgLen encUnary encUnary ∧
      IsPPTOn (encPair encUnary encBits) encBits (fun ⟨n, ct⟩ => A n ct) ∧
      ¬ Negligible (messageRecoveryWordAdvantage msgLen keyLen (otpKeyWordEncrypt keyLen) A) := by
  intro msgLen A
  refine ⟨demOneTimeKeyWordINDCPA_otpKeyWordEncrypt keyLen, ?_, ?_, ?_⟩
  · ppt
  · ppt
  · have hadv : ∀ n, messageRecoveryWordAdvantage msgLen keyLen
        (otpKeyWordEncrypt keyLen) A n = (1 : ℝ≥0) / 2 := by
      intro n
      have hfalse : ProbComp.eval (messageRecoveryWordExperiment msgLen keyLen
          (otpKeyWordEncrypt keyLen) A n) = PMF.pure false := by
        simp only [messageRecoveryWordExperiment, msgLen, A, ProbComp.eval_bind,
          ProbComp.eval_pure, BitString.eval_sampleList, PMF.pure_bind, PMF.bind_const]
        trans (BitString.uniformList 1).bind fun _ => PMF.pure false
        · refine Probability.PMF.bind_congr_on_support _ _ _ fun m hm => ?_
          have hlen : m.length = 1 := BitString.length_of_mem_support_uniformList hm
          have hne : ([] == m) = false := by
            simp only [beq_eq_false_iff_ne]
            intro heq
            have := congrArg List.length heq
            simp [hlen] at this
          simp [hne]
        · simp [PMF.bind_const]
      have hsucc : Game.succProbability (ProbComp.eval
          (messageRecoveryWordExperiment msgLen keyLen (otpKeyWordEncrypt keyLen) A n)) = 0 := by
        rw [hfalse]
        apply NNReal.coe_injective
        simp [Game.coe_succProbability]
      rw [messageRecoveryWordAdvantage, hsucc]
      apply NNReal.coe_injective
      rw [coe_nndist, NNReal.dist_eq]
      norm_num [msgLen, abs_of_neg]
    intro hneg
    exact not_negligible_const (by norm_num : (1 : ℝ≥0) / 2 ≠ 0)
      (hneg.congr fun n => hadv n)

end Counterexamples

end CslibFrontierTests.Crypto.MessageRecovery
