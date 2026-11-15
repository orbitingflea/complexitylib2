/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Basic
public import CslibFrontier.Crypto.Encoding
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Deterministic public-key encryption is not semantically secure

In a public-key encryption scheme, the adversary receives the public key and can encrypt any
message itself. If encryption is deterministic, the adversary of
[Boneh and Shoup, Section 11.3.1, pp. 438–439][BonehShoup2023] submits two distinct challenge
messages `(m₀, m₁)`, receives the challenge ciphertext `c`, computes `c₀ ← E(pk, m₀)` under the
public key it saved, and outputs `false` (`0`) when `c = c₀` and `true` (`1`) otherwise. In
experiment `false` it outputs `false` with probability `1`; in experiment `true` it outputs `true`
with probability `1`, so its semantic-security advantage is `1`.

This module formalizes that adversary and its analysis at both layers of the public-key encryption
API:

* For one fixed scheme `E : PKE PK SK M C`, `PKE.detAdversary E m₀ m₁` plays the two-stage
  chosen-plaintext experiment `E.cpaExperiment valid`
  (`CslibFrontier/Crypto/Computational/Encryption/Scheme.lean`).
* Over encoded families at a security parameter `n`, `Encryption.detAdversary encrypt m₀ m₁` is the
  word-level `Encryption.AdversaryOf Msg`
  (`CslibFrontier/Crypto/Computational/Encryption/Basic.lean`), certified uniform strict PPT by
  `Encryption.isPPT_detAdversary` from the PPT certificate of `encrypt` and polynomial-time
  certificates of `m₀` and `m₁`.

The hypotheses relate to [BonehShoup2023], Section 11.3.1, as follows.
`CslibFrontierTests.Crypto.DeterministicPKE` has checked instances showing that correctness,
admissibility, `m₀ ≠ m₁` and determinism are each needed.

* **Correctness is a hypothesis.** Definition 11.1 (p. 436) requires of every scheme that
  decryption undoes encryption, so the scheme of Section 11.3.1 is correct. Here `PKE` is a bare
  triple and `PKE.Correct` a separate predicate, so `Encryption.not_indcpaOn_of_deterministic`
  assumes `PKE.Correct` of `(keyGen n, encrypt n, decrypt n)`. The argument uses correctness only
  for `b = 1`, as disjointness of the ciphertext supports of `m₀` and `m₁` under honest public
  keys (`hne`, by `PKE.Correct.notMem_support_encrypt`); `PKE.eval_cpaExperiment_detAdversary_true`,
  `PKE.advantage_cpaExperiment_detAdversary` and `Encryption.advantage_gameOn_detAdversary` assume
  `hne` directly.
* **Only the encryption of `m₀` must be deterministic.** The book assumes the entire encryption
  algorithm is deterministic, whereas its argument uses only that `encrypt pk m₀` is a point mass
  (`PMF.pure c`) under every supported key pair (`hdet`), so the theorem also applies to schemes
  that randomize other messages.
* **Challenge-pair admissibility and an asymptotic threshold `n₀`.** Admissibility is parameterized
  by `valid`, required to hold on `(m₀, m₁)` under supported keys (`hvalid`), and in
  `Encryption.not_indcpaOn_of_deterministic` the hypotheses hold from a threshold parameter `n₀`
  onward (`n₀ ≤ n`).
* **Parameter-indexed challenge messages.** In `Encryption.detAdversary`, the messages
  `m₀, m₁ : ℕ → Msg` depend on the security parameter `n` alone rather than the public key.

## Main definitions

* `Cslib.Crypto.PKE.detAdversary`: the two-stage adversary of [BonehShoup2023], Section 11.3.1, for
  a fixed scheme `E : PKE PK SK M C`.
* `Cslib.Crypto.Encryption.detAdversary`: the word-level chosen-message adversary of
  [BonehShoup2023], Section 11.3.1, for message families `m₀ m₁ : ℕ → Msg`.

## Main results

* `Cslib.Crypto.PKE.eval_cpaExperiment_detAdversary_false`,
  `Cslib.Crypto.PKE.eval_cpaExperiment_detAdversary_true`,
  `Cslib.Crypto.PKE.advantage_cpaExperiment_detAdversary`: in `PKE.cpaExperiment`, `detAdversary`
  outputs `false` in world `false` when encryption of `m₀` is deterministic, outputs `true` in
  world `true` when `(m₀, m₁)` is admissible and the ciphertext supports of `m₀` and `m₁` are
  disjoint, and therefore has advantage `1` ([BonehShoup2023], Section 11.3.1, pp. 438–439).
* `Cslib.Crypto.PKE.Correct.notMem_support_encrypt`: in a correct scheme, distinct messages have
  disjoint ciphertext supports under every supported key pair.
* `Cslib.Crypto.Encryption.isPPT_detAdversary`: `detAdversary` is uniform strict PPT when
  encryption is PPT and `m₀`, `m₁` are computable in polynomial time.
* `Cslib.Crypto.Encryption.advantage_gameOn_detAdversary`: at parameter `n`, the word-level
  `detAdversary` achieves `gameOn` advantage `1`.
* `Cslib.Crypto.Encryption.not_indcpaOn_of_deterministic`: a public-key encryption scheme that is
  correct from some parameter `n₀` onward and admits two distinct polynomial-time challenge
  messages, the first encrypted deterministically, is not `INDCPAOn`
  ([BonehShoup2023], Section 11.3.1, pp. 438–439).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.2 (Definition 11.1, Attack Game 11.1, Definition 11.2,
  pp. 436–437) and Section 11.3.1 (pp. 438–439).
-/

public section

open Cslib Probability Turing.MultiTapeTM

namespace Cslib.Crypto

/-! ## Typed layer -/

namespace PKE

variable {PK SK M C : Type}

/-- The adversary of [BonehShoup2023], Section 11.3.1 (p. 438), against a fixed scheme `E`:
challenge with `(m₀, m₁)`, save the public key `pk`, re-encrypt `m₀` under `pk`, and output
`false` (`0`) when the challenge equals that ciphertext and `true` (`1`) otherwise. -/
@[expose] def detAdversary [BEq C] (E : PKE PK SK M C) (m₀ m₁ : M) :
    TwoStage PK (MessagePair M) C Bool PK where
  choose pk := pure (⟨m₀, m₁⟩, pk)
  guess pk c := do
    let c₀ ← E.encrypt pk m₀
    return c != c₀

/-- In experiment `false`, if `E.encrypt keys.1 m₀` is deterministic (a point mass) on every
supported key pair `keys`, then `E.detAdversary m₀ m₁` outputs `false` with probability `1`
([BonehShoup2023], Section 11.3.1, p. 438). -/
theorem eval_cpaExperiment_detAdversary_false [BEq C] [LawfulBEq C] (E : PKE PK SK M C)
    (valid : PK → M → M → Bool) {m₀ m₁ : M}
    (hdet : ∀ keys ∈ (ProbComp.eval E.keyGen).support,
      ∃ c, ProbComp.eval (E.encrypt keys.1 m₀) = PMF.pure c) :
    ProbComp.eval (E.cpaExperiment valid (E.detAdversary m₀ m₁) false) = PMF.pure false := by
  simp only [cpaExperiment, ProbComp.eval_bind]
  refine PMF.bind_eq_pure_of_forall_mem_support fun keys hkeys => ?_
  obtain ⟨c, hc⟩ := hdet keys hkeys
  by_cases hv : valid keys.1 m₀ m₁ = true <;>
    simp [lrExperiment, detAdversary, hv, hc]

/-- In experiment `true`, if `(m₀, m₁)` is admissible and no ciphertext in the support of
`E.encrypt keys.1 m₁` belongs to the support of `E.encrypt keys.1 m₀` on any supported key pair
`keys`, then `E.detAdversary m₀ m₁` outputs `true` with probability `1`
([BonehShoup2023], Section 11.3.1, p. 438). -/
theorem eval_cpaExperiment_detAdversary_true [BEq C] [LawfulBEq C] (E : PKE PK SK M C)
    (valid : PK → M → M → Bool) {m₀ m₁ : M}
    (hvalid : ∀ keys ∈ (ProbComp.eval E.keyGen).support, valid keys.1 m₀ m₁ = true)
    (hne : ∀ keys ∈ (ProbComp.eval E.keyGen).support,
      ∀ c₁ ∈ (ProbComp.eval (E.encrypt keys.1 m₁)).support,
        c₁ ∉ (ProbComp.eval (E.encrypt keys.1 m₀)).support) :
    ProbComp.eval (E.cpaExperiment valid (E.detAdversary m₀ m₁) true) = PMF.pure true := by
  simp only [cpaExperiment, ProbComp.eval_bind]
  refine PMF.bind_eq_pure_of_forall_mem_support fun keys hkeys => ?_
  simp only [lrExperiment, detAdversary, pure_bind, hvalid keys hkeys, ↓reduceIte,
    MessagePair.select_true, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_eq_pure_of_forall_mem_support fun c₁ hc₁ => ?_
  refine PMF.bind_eq_pure_of_forall_mem_support fun c₀ hc₀ => ?_
  have : c₁ ≠ c₀ := fun h => hne keys hkeys c₁ hc₁ (h ▸ hc₀)
  rw [show (c₁ != c₀) = true from bne_iff_ne.mpr this]

/-- Under the hypotheses of `eval_cpaExperiment_detAdversary_false` and
`eval_cpaExperiment_detAdversary_true`, `E.detAdversary m₀ m₁` achieves chosen-plaintext advantage
`1` ([BonehShoup2023], Section 11.3.1, pp. 438–439). -/
theorem advantage_cpaExperiment_detAdversary [BEq C] [LawfulBEq C] (E : PKE PK SK M C)
    (valid : PK → M → M → Bool) {m₀ m₁ : M}
    (hvalid : ∀ keys ∈ (ProbComp.eval E.keyGen).support, valid keys.1 m₀ m₁ = true)
    (hdet : ∀ keys ∈ (ProbComp.eval E.keyGen).support,
      ∃ c, ProbComp.eval (E.encrypt keys.1 m₀) = PMF.pure c)
    (hne : ∀ keys ∈ (ProbComp.eval E.keyGen).support,
      ∀ c₁ ∈ (ProbComp.eval (E.encrypt keys.1 m₁)).support,
        c₁ ∉ (ProbComp.eval (E.encrypt keys.1 m₀)).support) :
    Experiment.advantage (E.cpaExperiment valid (E.detAdversary m₀ m₁) false)
      (E.cpaExperiment valid (E.detAdversary m₀ m₁) true) = 1 := by
  rw [Experiment.advantage, eval_cpaExperiment_detAdversary_false E valid hdet,
    eval_cpaExperiment_detAdversary_true E valid hvalid hne]
  simp [Game.advantage, Game.succProbability]

/-- A correct scheme never encrypts two distinct messages to the same ciphertext under any
supported key pair. -/
theorem Correct.notMem_support_encrypt {E : PKE PK SK M C} (hE : E.Correct) {m₀ m₁ : M}
    (hm : m₀ ≠ m₁) {keys : PK × SK} (hkeys : keys ∈ (ProbComp.eval E.keyGen).support) {c : C}
    (hc : c ∈ (ProbComp.eval (E.encrypt keys.1 m₁)).support) :
    c ∉ (ProbComp.eval (E.encrypt keys.1 m₀)).support := fun hc₀ =>
  hm (Option.some.inj ((hE keys hkeys m₀ c hc₀).symm.trans (hE keys hkeys m₁ c hc)))

end PKE

/-! ## Word level -/

namespace Encryption

variable {Msg : Type}

/-- The word-level adversary of [BonehShoup2023], Section 11.3.1 (p. 438): at security parameter
`n`, challenge with `(m₀ n, m₁ n)`, save the public key `pk` as the state word, re-encrypt `m₀ n`
under `pk`, and output `c != c₀`. -/
def detAdversary (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (m₀ m₁ : ℕ → Msg) :
    AdversaryOf Msg where
  choose n pk := pure ((m₀ n, m₁ n), pk)
  guess n pk c := do
    let c₀ ← encrypt n pk (m₀ n)
    return c != c₀

/-- `detAdversary encrypt m₀ m₁` is uniform strict PPT whenever `encrypt` is PPT on
`encKeyedInput encMsg` and `m₀`, `m₁` are computable in polynomial time from the unary security
parameter. -/
theorem isPPT_detAdversary {encMsg : Msg ↪ List Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)} {m₀ m₁ : ℕ → Msg}
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, pk, msg⟩ => encrypt n pk msg))
    (hm₀ : ComputableInPolyTime m₀ encUnary encMsg)
    (hm₁ : ComputableInPolyTime m₁ encUnary encMsg) :
    (detAdversary encrypt m₀ m₁).IsPPT encMsg where
  choose := by
    unfold detAdversary
    ppt
  guess := by
    unfold detAdversary
    ppt

/-- At security parameter `n`, the two-stage form of `detAdversary encrypt m₀ m₁` is the typed
`PKE.detAdversary` of `(keyGen n, encrypt n, decrypt)` with messages `m₀ n` and `m₁ n`. -/
private theorem toTwoStage_detAdversary (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : List Bool → List Bool → Option Msg) (m₀ m₁ : ℕ → Msg) (n : ℕ) :
    (detAdversary encrypt m₀ m₁).toTwoStage n =
      (PKE.mk (keyGen n) (encrypt n) decrypt).detAdversary (m₀ n) (m₁ n) := by
  simp [AdversaryOf.toTwoStage, detAdversary, PKE.detAdversary]

/-- At security parameter `n`, `detAdversary encrypt m₀ m₁` achieves `gameOn` advantage `1` when
`(m₀ n, m₁ n)` is admissible, encryption of `m₀ n` is deterministic, and the ciphertext supports of
`m₀ n` and `m₁ n` are disjoint under every supported key pair ([BonehShoup2023], Section 11.3.1,
pp. 438–439). -/
theorem advantage_gameOn_detAdversary (valid : ℕ → List Bool → Msg → Msg → Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)) (m₀ m₁ : ℕ → Msg) (n : ℕ)
    (hvalid : ∀ keys ∈ (ProbComp.eval (keyGen n)).support, valid n keys.1 (m₀ n) (m₁ n) = true)
    (hdet : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∃ c, ProbComp.eval (encrypt n keys.1 (m₀ n)) = PMF.pure c)
    (hne : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ c₁ ∈ (ProbComp.eval (encrypt n keys.1 (m₁ n))).support,
        c₁ ∉ (ProbComp.eval (encrypt n keys.1 (m₀ n))).support) :
    advantage (gameOn valid keyGen encrypt (detAdversary encrypt m₀ m₁)) n = 1 := by
  rw [advantage_gameOn_eq_cpaExperiment valid keyGen encrypt (fun _ _ => none),
    toTwoStage_detAdversary keyGen]
  exact PKE.advantage_cpaExperiment_detAdversary _ _ hvalid hdet hne

/-- **A deterministic public-key encryption scheme is not semantically secure**
([BonehShoup2023], Section 11.3.1, pp. 438–439): if `encrypt` is PPT, `m₀` and `m₁` are computable
in polynomial time, and from some parameter `n₀` onward the scheme is correct, `m₀ n ≠ m₁ n`, the
pair `(m₀ n, m₁ n)` is admissible under every supported public key, and `encrypt n pk (m₀ n)` is
deterministic under every supported public key, then the scheme fails `INDCPAOn valid encMsg`. -/
theorem not_indcpaOn_of_deterministic {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    (decrypt : ℕ → List Bool → List Bool → Option Msg) {m₀ m₁ : ℕ → Msg} (n₀ : ℕ)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits (fun ⟨n, pk, msg⟩ => encrypt n pk msg))
    (hm₀ : ComputableInPolyTime m₀ encUnary encMsg)
    (hm₁ : ComputableInPolyTime m₁ encUnary encMsg)
    (hcorrect : ∀ n, n₀ ≤ n → (PKE.mk (keyGen n) (encrypt n) (decrypt n)).Correct)
    (hm : ∀ n, n₀ ≤ n → m₀ n ≠ m₁ n)
    (hvalid : ∀ n, n₀ ≤ n → ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (m₀ n) (m₁ n) = true)
    (hdet : ∀ n, n₀ ≤ n → ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∃ c, ProbComp.eval (encrypt n keys.1 (m₀ n)) = PMF.pure c) :
    ¬ INDCPAOn valid encMsg keyGen encrypt := by
  intro h
  have hneg := (h _ (isPPT_detAdversary hencrypt hm₀ hm₁)).shift n₀
  refine not_negligible_const one_ne_zero (hneg.congr fun n => ?_)
  exact advantage_gameOn_detAdversary valid keyGen encrypt m₀ m₁ (n + n₀)
    (hvalid _ (by omega)) (hdet _ (by omega)) fun keys hkeys c hc =>
      (hcorrect _ (by omega)).notMem_support_encrypt (hm _ (by omega)) hkeys hc

end Encryption

end Cslib.Crypto
