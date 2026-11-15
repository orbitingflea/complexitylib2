/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Crypto.Protocols.PerfectSecrecy.Basic
public import CslibFrontier.Crypto.Computational.Encryption.Cipher
public import CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers
public import Mathlib.Data.FinEnum
import Cslib.Crypto.Protocols.PerfectSecrecy.OneTimePad

/-!
# Equal Ciphertext Laws and Semantic Security of One-Time Pads

This module derives one-time semantic security (`Cipher.oneTimeExperiment` advantage `0`) for
ciphers whose key-averaged ciphertext distribution is invariant across admissible message pairs
([BonehShoup2023], Example 2.9, p. 17; Exercise 2.7, p. 39), without restricting to deterministic
ciphers.

Connecting an information-theoretic `EncScheme` to a computational `Cipher` and key sampler via
distribution equality yields zero semantic-security advantage for every cipher matching an
`EncScheme.PerfectlySecret` scheme (and clients holding `EncScheme.CiphertextIndist` directly apply
`advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq` with `ciphertextDist_eq_encScheme`).
Instantiations cover both the fixed-length one-time pad over `BitVec l` and the variable-length
one-time pad `variableLengthOTPCipher L` on equal-length messages.

For the bit-guessing identity `SSadv[A, E] = 2 * SSadv*[A, E]` ([BonehShoup2023], Theorem 2.10,
p. 26) applied to `E.oneTimeExperiment sampleKey valid A`, apply
`Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit` from
`CslibFrontier.Crypto.Game.HiddenBit` directly.

## Main definitions

- `Cslib.Crypto.Cipher.ciphertextDist`: key-averaged ciphertext law of a `Cipher` under a key
  sampler `sampleKey`
- `Cslib.Crypto.Cipher.ofPure`: deterministic `Cipher` from pure encryption and decryption maps
- `Cslib.Crypto.Cipher.otpCipher`: fixed-length one-time pad over `BitVec l` as a `Cipher`
- `Cslib.Crypto.Cipher.variableLengthOTPCipher`: variable-length one-time pad on boolean lists of
  length at most `L` as a `Cipher`

## Main results

- `Cslib.Crypto.Cipher.eval_oneTimeExperiment_eq_of_ciphertextDist_eq`: equal ciphertext laws on
  admissible message pairs induce identical experiment distributions for both challenge bits against
  every adversary
- `Cslib.Crypto.Cipher.advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq`: equal ciphertext
  laws on admissible pairs give semantic-security advantage `0` against every adversary
- `Cslib.Crypto.Cipher.advantage_oneTimeExperiment_eq_zero_of_perfectlySecret`: any cipher matching
  a `PerfectlySecret` scheme has semantic-security advantage `0` against every adversary
- `Cslib.Crypto.Cipher.advantage_oneTimeExperiment_otpCipher`: semantic-security advantage `0` for
  `otpCipher l` with a uniform key
- `Cslib.Crypto.Cipher.advantage_oneTimeExperiment_variableLengthOTPCipher`: semantic-security
  advantage `0` for `variableLengthOTPCipher L` on equal-length messages

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, v0.6][BonehShoup2023]
-/

public section

namespace Cslib.Crypto.Cipher

open Cslib.Probability
open Cslib.Crypto.Protocols.PerfectSecrecy

variable {K M C : Type}

/-- The key-averaged ciphertext distribution of `m` under cipher `E` when keys are drawn from
`sampleKey`. -/
@[expose]
noncomputable def ciphertextDist (E : Cipher K M C) (sampleKey : ProbComp K) (m : M) : PMF C :=
  (ProbComp.eval sampleKey).bind fun k => ProbComp.eval (E.encrypt k m)

/-- Build a symmetric cipher from deterministic pure encryption and decryption functions. -/
@[expose]
def ofPure (enc : K → M → C) (dec : K → C → M) : Cipher K M C where
  encrypt k m := pure (enc k m)
  decrypt k c := some (dec k c)

/-- A deterministic cipher `ofPure enc dec` is correct when `dec k` is a left inverse of
`enc k` for every key `k`. -/
theorem ofPure_correct (enc : K → M → C) (dec : K → C → M)
    (h : ∀ k, Function.LeftInverse (dec k) (enc k)) :
    (ofPure enc dec).Correct := by
  intro k m c hc
  simp only [ofPure, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hc
  subst hc
  exact congrArg some (h k m)

/-- Key-averaged ciphertext distribution of a deterministic cipher `ofPure enc dec`. -/
@[simp]
theorem ciphertextDist_ofPure (enc : K → M → C) (dec : K → C → M)
    (sampleKey : ProbComp K) (m : M) :
    (ofPure enc dec).ciphertextDist sampleKey m = (ProbComp.eval sampleKey).map (enc · m) := by
  simp only [ciphertextDist, ofPure, ProbComp.eval_pure]
  rfl

/-- **Equal ciphertext laws hide the challenge bit**: if the key-averaged ciphertext law of `m₀`
equals that of `m₁` for every admissible pair `(m₀, m₁)`, then `oneTimeExperiment` has the same
output distribution for both challenge bits against every adversary. -/
theorem eval_oneTimeExperiment_eq_of_ciphertextDist_eq {σ : Type} (E : Cipher K M C)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (h : ∀ m₀ m₁, valid m₀ m₁ = true →
      E.ciphertextDist sampleKey m₀ = E.ciphertextDist sampleKey m₁)
    (A : TwoStage Unit (MessagePair M) C Bool σ) (b₀ b₁ : Bool) :
    ProbComp.eval (E.oneTimeExperiment sampleKey valid A b₀) =
      ProbComp.eval (E.oneTimeExperiment sampleKey valid A b₁) := by
  simp only [Cipher.oneTimeExperiment, ProbComp.eval_bind, eval_lrExperiment]
  rw [PMF.bind_comm]
  conv_rhs => rw [PMF.bind_comm]
  congr 1 with choice : 1
  split
  · rename_i hvalid
    rw [← PMF.bind_bind, ← PMF.bind_bind]
    have hdist : E.ciphertextDist sampleKey (choice.1.select b₀) =
        E.ciphertextDist sampleKey (choice.1.select b₁) := by
      cases b₀ <;> cases b₁ <;>
        simp only [MessagePair.select_false, MessagePair.select_true, h _ _ hvalid]
    exact congrArg (fun law : PMF C => law.bind fun c => ProbComp.eval (A.guess choice.2 c)) hdist
  · rfl

/-- **Equal ciphertext laws give zero semantic-security advantage** ([BonehShoup2023],
Example 2.9, p. 17; Exercise 2.7, p. 39). -/
theorem advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq {σ : Type} (E : Cipher K M C)
    (sampleKey : ProbComp K) (valid : M → M → Bool)
    (h : ∀ m₀ m₁, valid m₀ m₁ = true →
      E.ciphertextDist sampleKey m₀ = E.ciphertextDist sampleKey m₁)
    (A : TwoStage Unit (MessagePair M) C Bool σ) :
    Experiment.advantage (E.oneTimeExperiment sampleKey valid A false)
      (E.oneTimeExperiment sampleKey valid A true) = 0 := by
  rw [Experiment.advantage,
    eval_oneTimeExperiment_eq_of_ciphertextDist_eq E sampleKey valid h A false true,
    Game.advantage_self]

/-- A cipher whose key sampler and encryption laws match an information-theoretic `EncScheme`
has the same ciphertext distribution as that scheme. -/
theorem ciphertextDist_eq_encScheme (E : Cipher K M C) (sampleKey : ProbComp K)
    (S : EncScheme M K C)
    (hgen : S.gen = ProbComp.eval sampleKey)
    (henc : ∀ k m, ProbComp.eval (E.encrypt k m) = S.enc k m) (m : M) :
    E.ciphertextDist sampleKey m = S.ciphertextDist m := by
  simp only [ciphertextDist, EncScheme.ciphertextDist, hgen]
  congr 1
  funext k
  exact henc k m

/-- **Ciphers matching a perfectly secret `EncScheme` have zero semantic-security advantage**:
any `Cipher` matching an `EncScheme.PerfectlySecret` scheme through `hgen` and `henc` has
advantage `0` in `oneTimeExperiment` against every adversary ([BonehShoup2023], Example 2.9,
p. 17). -/
theorem advantage_oneTimeExperiment_eq_zero_of_perfectlySecret {σ : Type} (E : Cipher K M C)
    (sampleKey : ProbComp K) (S : EncScheme M K C)
    (hgen : S.gen = ProbComp.eval sampleKey)
    (henc : ∀ k m, ProbComp.eval (E.encrypt k m) = S.enc k m)
    (hS : S.PerfectlySecret) (valid : M → M → Bool)
    (A : TwoStage Unit (MessagePair M) C Bool σ) :
    Experiment.advantage (E.oneTimeExperiment sampleKey valid A false)
      (E.oneTimeExperiment sampleKey valid A true) = 0 := by
  refine advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq E sampleKey valid
    (fun m₀ m₁ _ => ?_) A
  rw [ciphertextDist_eq_encScheme E sampleKey S hgen henc m₀,
    ciphertextDist_eq_encScheme E sampleKey S hgen henc m₁]
  exact (EncScheme.perfectlySecret_iff_ciphertextIndist S).mp hS m₀ m₁

/-- The fixed-length one-time pad over `BitVec l` as a `Cipher`. -/
@[expose]
def otpCipher (l : ℕ) : Cipher (BitVec l) (BitVec l) (BitVec l) :=
  ofPure (fun k m => k ^^^ m) (fun k c => k ^^^ c)

/-- Correctness of the fixed-length one-time pad cipher `otpCipher l`. -/
theorem otpCipher_correct (l : ℕ) : (otpCipher l).Correct :=
  ofPure_correct _ _ fun k m => by
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- **The one-time pad has zero semantic-security advantage** under a uniform key against every
adversary ([BonehShoup2023], Example 2.9, p. 17). -/
theorem advantage_oneTimeExperiment_otpCipher {σ : Type} (l : ℕ)
    (valid : BitVec l → BitVec l → Bool)
    (A : TwoStage Unit (MessagePair (BitVec l)) (BitVec l) Bool σ) :
    Experiment.advantage
        ((otpCipher l).oneTimeExperiment (ProbComp.uniform (BitVec l)) valid A false)
        ((otpCipher l).oneTimeExperiment (ProbComp.uniform (BitVec l)) valid A true) = 0 :=
  advantage_oneTimeExperiment_eq_zero_of_perfectlySecret (otpCipher l)
    (ProbComp.uniform (BitVec l)) (otp l)
    (ProbComp.eval_uniform (BitVec l)).symm (fun _ _ => ProbComp.eval_pure _)
    (otp_perfectlySecret l) valid A

/-- The variable-length one-time pad on words of length at most `L` as a `Cipher`. -/
@[expose]
def variableLengthOTPCipher (L : ℕ) :
    Cipher (BitString L) {w : List Bool // w.length ≤ L} {w : List Bool // w.length ≤ L} :=
  ofPure (varXor L) (varXor L)

/-- Correctness of the variable-length one-time pad cipher `variableLengthOTPCipher L`. -/
theorem variableLengthOTPCipher_correct (L : ℕ) : (variableLengthOTPCipher L).Correct :=
  ofPure_correct _ _ (varXor_varXor L)

/-- **The variable-length one-time pad has zero semantic-security advantage on equal-length
messages** under a uniform key against every adversary ([BonehShoup2023], Example 2.9, p. 17;
Exercise 2.7, p. 39). -/
theorem advantage_oneTimeExperiment_variableLengthOTPCipher {σ : Type} (L : ℕ)
    (A : TwoStage Unit (MessagePair {w : List Bool // w.length ≤ L})
      {w : List Bool // w.length ≤ L} Bool σ) :
    Experiment.advantage
        ((variableLengthOTPCipher L).oneTimeExperiment (ProbComp.uniform (BitString L))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A false)
        ((variableLengthOTPCipher L).oneTimeExperiment (ProbComp.uniform (BitString L))
          (fun m₀ m₁ => decide (m₀.1.length = m₁.1.length)) A true) = 0 := by
  refine advantage_oneTimeExperiment_eq_zero_of_ciphertextDist_eq _ _ _ (fun m₀ m₁ hm => ?_) A
  have hb := ciphertextDist_eq_encScheme (variableLengthOTPCipher L)
    (ProbComp.uniform (BitString L)) (variableLengthOTP L)
    (ProbComp.eval_uniform (BitString L)).symm (fun _ _ => ProbComp.eval_pure _)
  rw [hb, hb, variableLengthOTP_ciphertextDist_eq_iff]
  exact decide_eq_true_eq.mp hm

end Cslib.Crypto.Cipher

end
