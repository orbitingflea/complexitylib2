/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CCA
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Malleable encryption is not CCA secure

A public-key scheme is *malleable* when anyone can transform a ciphertext into a different
ciphertext whose plaintext is a known function of the original one. Such a scheme is not CCA
secure: the adversary asks the Phase 2 decryption oracle to decrypt the transformed challenge, which
the oracle must answer because it differs from the challenge, and reads off the hidden bit
([BonehShoup2023], Section 12.2.1, pp. 469–470, which describes this adversary and notes that it has
advantage `1`).

`maulAdversary msg₀ msg₁ maul target` is that adversary for the single-challenge game
`Encryption.cca2GameOn`. Phase 1 makes no query, chooses `(msg₀ n pk, msg₁ n pk)` and saves the
public key. Phase 2 queries the decryption oracle once, on `maul n pk ct`, and outputs whether the
reply is the word `target n pk`, reading only a reply prefix one bit longer than `target n pk`.
A scheme instantiates it by supplying its transformation and the reply that world `1` produces.

## Main definitions

* `Cslib.Crypto.Encryption.maulAdversary`: the one-query malleability adversary.

## Main results

* `Cslib.Crypto.Encryption.isPPT_maulAdversary`: the adversary is strict oracle PPT when its
  message choices, transformation and target are polynomial-time.
* `Cslib.Crypto.Encryption.eval_cca2GameOn_maulAdversary`: if the challenge pair is admissible
  under every honest public key, and on every honest key pair and challenge ciphertext of world
  `bit` the transformation changes the decryption and yields `target` exactly when `bit = true`,
  then world `bit` outputs `bit` with probability `1`.
* `Cslib.Crypto.Encryption.not_indcca2On_of_maulAdversary`: under these conditions at every
  parameter, the scheme fails `INDCCA2On`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definition 12.2, pp. 467–468) and
  Section 12.2.1 (pp. 469–470).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM

/-- **The one-query malleability adversary** ([BonehShoup2023], Section 12.2.1, pp. 469–470).
Phase 1 makes no query, chooses `(msg₀ n pk, msg₁ n pk)` and saves the public key `pk` as its
state. Phase 2 queries the decryption oracle once on `maul n pk ct` and outputs whether the reply
is `target n pk`; it reads only a reply prefix one bit longer than `target n pk`. -/
def maulAdversary {Msg : Type} (msg₀ msg₁ : ℕ → List Bool → Msg)
    (maul : ℕ → List Bool → List Bool → List Bool) (target : ℕ → List Bool → List Bool) :
    CCA2AdversaryOf Msg where
  choose n pk := pure ((msg₀ n pk, msg₁ n pk), pk)
  guess n pk ct := do
    let reply ← List.take ((target n pk).length + 1) <$>
      ProbOracleComp.query ((), maul n pk ct)
    return reply == target n pk

/-- `maulAdversary` is strict oracle PPT whenever its message choices, transformation and target
are computable in polynomial time. -/
theorem isPPT_maulAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {maul : ℕ → List Bool → List Bool → List Bool}
    {target : ℕ → List Bool → List Bool}
    (hmsg₀ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₀ n pk) (encPair encUnary encBits) encMsg)
    (hmsg₁ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₁ n pk) (encPair encUnary encBits) encMsg)
    (hmaul : ComputableInPolyTime (fun ⟨n, pk, ct⟩ => maul n pk ct) encGuessInput encBits)
    (htarget : ComputableInPolyTime (fun ⟨n, pk⟩ => target n pk) (encPair encUnary encBits)
      encBits) :
    (maulAdversary msg₀ msg₁ maul target).IsPPT encMsg where
  choose :=
    ((hmsg₀.prod hmsg₁).prod (ComputableInPolyTime.snd encUnary encBits)).isOraclePPTOn.isOraclePPT
  guess := by
    have hst : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => (p.1, p.2.1))
        encGuessInput (encPair encUnary encBits) := by
      fun_prop
    have ht := htarget.comp hst
    have hout : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool => p.2 == target p.1.1 p.1.2.1)
        (encPair encGuessInput encBits) encBool :=
      (ComputableInPolyTime.snd encGuessInput encBits).beq
        (ht.comp (ComputableInPolyTime.fst encGuessInput encBits))
    exact (IsOraclePPTOn.query_take' () hmaul (by fun_prop)).bind_with hout.isOraclePPTOn

/-- Reading a prefix one bit longer than `l` decides equality with `l`. -/
private theorem take_length_succ_beq (l r : List Bool) :
    (List.take (l.length + 1) r == l) = decide (r = l) := by
  by_cases h : r = l
  · subst h
    simp only [List.take_of_length_le (Nat.le_succ _), beq_self_eq_true, decide_true]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro htake
    have hlen := congrArg List.length htake
    rw [List.length_take] at hlen
    exact h (by rwa [List.take_of_length_le (by omega)] at htake)

/-- **A malleable scheme loses the 1CCA game with certainty** ([BonehShoup2023],
Section 12.2.1, pp. 469–470). Suppose the challenge pair of `maulAdversary` is admissible under
every honest public key and that, for every honest key pair and every challenge ciphertext `ct` of
world `bit`, the transformation `maul` changes the decryption of `ct` and its decryption encodes to
`target` exactly when `bit = true`. Then world `bit` outputs `bit` with probability `1`. -/
theorem eval_cca2GameOn_maulAdversary {Msg Out : Type} {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encOut : Out ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {maul : ℕ → List Bool → List Bool → List Bool}
    {target : ℕ → List Bool → List Bool} {n : ℕ} {bit : Bool}
    (hvalid : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (msg₀ n keys.1) (msg₁ n keys.1) = true)
    (hmaul : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval
        (encrypt n keys.1 (if bit then msg₁ n keys.1 else msg₀ n keys.1))).support,
        decrypt n keys.2 (maul n keys.1 ct) ≠ decrypt n keys.2 ct ∧
          (encOption encOut (decrypt n keys.2 (maul n keys.1 ct)) = target n keys.1 ↔
            bit = true)) :
    ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt
      (maulAdversary msg₀ msg₁ maul target) bit n) = PMF.pure bit := by
  simp only [cca2GameOn, maulAdversary, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs,
    ChoiceOut.state, ProbComp.eval_bind, runWith_norm, pmf_norm]
  rw [← PMF.bind_const (ProbComp.eval (keyGen n)) (PMF.pure bit)]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  simp only [hvalid keys hkeys, ↓reduceIte, ProbComp.eval_bind]
  rw [← PMF.bind_const (ProbComp.eval (encrypt n keys.1 _)) (PMF.pure bit)]
  refine PMF.bind_congr_on_support _ _ _ fun ct hct => ?_
  obtain ⟨hne, hiff⟩ := hmaul keys hkeys ct hct
  have hct' : (maul n keys.1 ct == ct) = false :=
    beq_eq_false_iff_ne.mpr fun h => hne (by rw [h])
  simp only [cca2Phase2Oracle, hct', Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure,
    runWith_norm, pmf_norm, take_length_succ_beq]
  exact congrArg PMF.pure (Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using hiff))

/-- Under the hypotheses of `eval_cca2GameOn_maulAdversary` for both worlds, `maulAdversary` has
1CCA advantage exactly `1`. -/
theorem advantage_cca2GameOn_maulAdversary {Msg Out : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encOut : Out ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {maul : ℕ → List Bool → List Bool → List Bool}
    {target : ℕ → List Bool → List Bool} {n : ℕ}
    (hvalid : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (msg₀ n keys.1) (msg₁ n keys.1) = true)
    (hmaul : ∀ bit, ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval
        (encrypt n keys.1 (if bit then msg₁ n keys.1 else msg₀ n keys.1))).support,
        decrypt n keys.2 (maul n keys.1 ct) ≠ decrypt n keys.2 ct ∧
          (encOption encOut (decrypt n keys.2 (maul n keys.1 ct)) = target n keys.1 ↔
            bit = true)) :
    Game.advantage
      (ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt
        (maulAdversary msg₀ msg₁ maul target) false n))
      (ProbComp.eval (cca2GameOn valid encOut keyGen encrypt decrypt
        (maulAdversary msg₀ msg₁ maul target) true n)) = 1 := by
  rw [eval_cca2GameOn_maulAdversary hvalid (hmaul false),
    eval_cca2GameOn_maulAdversary hvalid (hmaul true), Game.advantage_pure_false_left]
  simp [Game.succProbability]

/-- **A malleable scheme is not 1CCA secure** ([BonehShoup2023], Section 12.2.1, pp. 469–470):
if `maulAdversary msg₀ msg₁ maul target` has polynomial-time ingredients and satisfies the
hypotheses of `eval_cca2GameOn_maulAdversary` in both worlds at every parameter, then the scheme
fails `INDCCA2On valid encMsg encOut`. -/
theorem not_indcca2On_of_maulAdversary {Msg Out : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encMsg : Msg ↪ List Bool}
    {encOut : Out ↪ List Bool} {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    {msg₀ msg₁ : ℕ → List Bool → Msg} {maul : ℕ → List Bool → List Bool → List Bool}
    {target : ℕ → List Bool → List Bool}
    (hmsg₀ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₀ n pk) (encPair encUnary encBits) encMsg)
    (hmsg₁ : ComputableInPolyTime (fun ⟨n, pk⟩ => msg₁ n pk) (encPair encUnary encBits) encMsg)
    (hmaulPoly : ComputableInPolyTime (fun ⟨n, pk, ct⟩ => maul n pk ct) encGuessInput encBits)
    (htarget : ComputableInPolyTime (fun ⟨n, pk⟩ => target n pk) (encPair encUnary encBits)
      encBits)
    (hvalid : ∀ n, ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      valid n keys.1 (msg₀ n keys.1) (msg₁ n keys.1) = true)
    (hmaul : ∀ n bit, ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval
        (encrypt n keys.1 (if bit then msg₁ n keys.1 else msg₀ n keys.1))).support,
        decrypt n keys.2 (maul n keys.1 ct) ≠ decrypt n keys.2 ct ∧
          (encOption encOut (decrypt n keys.2 (maul n keys.1 ct)) = target n keys.1 ↔
            bit = true)) :
    ¬ INDCCA2On valid encMsg encOut keyGen encrypt decrypt := by
  intro hcca
  have hneg := hcca _ (isPPT_maulAdversary hmsg₀ hmsg₁ hmaulPoly htarget)
  simp only [advantage_cca2GameOn_maulAdversary (hvalid _) (hmaul _)] at hneg
  exact not_negligible_const one_ne_zero hneg

end Cslib.Crypto.Encryption
