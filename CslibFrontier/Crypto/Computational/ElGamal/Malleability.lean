/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Crypto.Computational.Encryption.CCA
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT

/-!
# Multiplicative ElGamal is not CCA secure

The native multiplicative ElGamal scheme of
`CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean`,
`(elGamalKeyGenProb d, elGamalEncryptProb encodeMsg d)` with decryption `elGamalDecryptDet d`,
is IND-CPA secure under DDH (`DDH.indcpa_elGamalBitEncryptProb`,
`DDH.indcpaOn_elGamalEncryptProb`), but it is malleable and therefore not CCA secure. This module
proves that unconditionally, by an explicit strict oracle-PPT adversary with 1CCA advantage exactly
`1` at every security parameter.

* **Statement ([BonehShoup2023], Exercise 12.1, printed p. 512), verbatim:** "Show that
  multiplicative ElGamal from Exercise 11.5 is not CCA secure. Your adversary should have an
  advantage of 1 in the 1CCA attack game."

Multiplicative ElGamal ([BonehShoup2023], Exercise 11.5, p. 459) encrypts `m` as
`(v, e) = (β • g, β • u + m)` (written additively) and decrypts `(v, e)` to `e - α • v`. The
adversary `elGamalMaulAdversary` submits two challenge messages encoding distinct group elements
`x₀ ≠ x₁`, maps the challenge ciphertext `(v, e)` to `(v, e + g)` (`elGamalMaulCiphertext`), which
differs from it because `g ≠ 0`, asks the Phase 2 decryption oracle for it, receives `x_b + g`, and
outputs whether this is `x₁ + g`.

## Mapping to the source

* The 1CCA game of [BonehShoup2023], Definition 12.2 (p. 468) is `Encryption.cca2GameOn`, and its
  advantage `|Pr[W₀] - Pr[W₁]|` is the two-world `Game.advantage`; the bound proved is exactly `1`,
  as the exercise asks (`advantage_cca2GameOn_elGamalMaulAdversary`).
* Exercise 11.5's message space is the group. The headline `not_indcca2Of_elGamalBitEncryptProb`
  restricts it to the two bit messages `0` and `g` (`encodeBit`), the scheme whose IND-CPA
  security `DDH.indcpa_elGamalBitEncryptProb` proves, and needs no hypothesis beyond a
  polynomial-time group family. The group-element scheme fails as well whenever its admissibility
  predicate admits the pair `(0, g)` under honest public keys
  (`not_indcca2On_elGamalGroupEncryptProb`). Both also fail the interleaved multi-challenge CCA
  notion of Definition 12.1 (`not_indcca2InterleavedOf_elGamalBitEncryptProb`,
  `not_indcca2InterleavedOn_elGamalGroupEncryptProb`).
* As in `CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean`, the group at parameter `n` is
  the fixed description `d n`, and key generation and encryption sample exponents with
  `F.sampleExp`. The attack succeeds for every key and every encryption coin, so these choices do
  not affect the result. Decryption never rejects, as in the source, so the CCA decryptor is
  `elGamalDecryptOpt d = some ∘ elGamalDecryptDet d`.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptOpt`: multiplicative ElGamal decryption as an
  `Option`-valued decryptor for the CCA games.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMaulCiphertext`: the word-level ciphertext map
  `(v, e) ↦ (v, e + g)`.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMaulAdversary`: the one-query 1CCA adversary.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMaulCiphertext_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalMaulCiphertext_ne`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet_elGamalMaulCiphertext`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_elGamalMaulCiphertext`: the mauled
  ciphertext differs from the original and decrypts to the message plus `g`; the map is
  polynomial-time.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_elGamalMaulAdversary`: the adversary is strict
  oracle PPT.
* `Cslib.Crypto.PrimeOrderGroupFamily.eval_cca2GameOn_elGamalMaulAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_cca2GameOn_elGamalMaulAdversary`: in world `b` the
  game outputs `b` with probability `1`, so the advantage is `1`.
* `Cslib.Crypto.PrimeOrderGroupFamily.not_indcca2On_elGamalEncryptProb`: general form, for any
  efficiently computable admissible pair of messages encoding distinct group elements.
* `Cslib.Crypto.PrimeOrderGroupFamily.not_indcca2Of_elGamalBitEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.not_indcca2InterleavedOf_elGamalBitEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.not_indcca2On_elGamalGroupEncryptProb`,
  `Cslib.Crypto.PrimeOrderGroupFamily.not_indcca2InterleavedOn_elGamalGroupEncryptProb`:
  multiplicative ElGamal is not CCA secure ([BonehShoup2023], Exercise 12.1, p. 512).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.5 (p. 459), Section 12.1 (Attack Game 12.1,
  Definitions 12.1–12.2, pp. 467–468), and Exercise 12.1 (p. 512).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Encryption

variable (F : PrimeOrderGroupFamily)

/-- Multiplicative ElGamal decryption as the `Option`-valued decryptor of the CCA games
(`Encryption.cca2GameOn`): it never rejects and returns `elGamalDecryptDet d n sk ct`, as the
decryption algorithm of [BonehShoup2023], Exercise 11.5 (p. 459) is defined on all of `G²`. -/
@[expose] def elGamalDecryptOpt (d : ℕ → F.Desc) (n : ℕ) (sk ct : List Bool) : Option (List Bool) :=
  some (F.elGamalDecryptDet d n sk ct)

/-- The word-level malleability map of multiplicative ElGamal: send an encoded ciphertext
`encPair encBits encBits (v, e)` to `encPair encBits encBits (v, F.add (d, e, encode g))`. On
encoded group elements it maps `(v, e)` to `(v, e + g)`, combining the ciphertext with the
randomness-free encryption `(0, g)` of `g` by the homomorphism of [BonehShoup2023],
Exercise 11.5(c) (p. 459). -/
@[expose] def elGamalMaulCiphertext (d : F.Desc) (ct : List Bool) : List Bool :=
  encPair encBits encBits (unframe ct, F.add (d, dropFrame ct, F.encode d (F.generator d)))

/-- On encoded group elements, `elGamalMaulCiphertext` maps `(v, e)` to `(v, e + g)`. -/
theorem elGamalMaulCiphertext_encode (d : F.Desc) (v e : F.Carrier d) :
    F.elGamalMaulCiphertext d (encPair encBits encBits (F.encode d v, F.encode d e)) =
      encPair encBits encBits (F.encode d v, F.encode d (e + F.generator d)) := by
  simp only [elGamalMaulCiphertext, unframe_encPair_encBits, dropFrame_encPair_encBits,
    F.add_encode]

/-- The mauled ciphertext of an encoded ciphertext differs from it, since `g ≠ 0`. -/
theorem elGamalMaulCiphertext_ne (d : F.Desc) (v e : F.Carrier d) :
    F.elGamalMaulCiphertext d (encPair encBits encBits (F.encode d v, F.encode d e)) ≠
      encPair encBits encBits (F.encode d v, F.encode d e) := by
  rw [elGamalMaulCiphertext_encode]
  intro h
  have he := (F.encode_injective d) (congrArg Prod.snd ((encPair encBits encBits).injective h))
  exact F.generator_ne_zero d (add_eq_left.mp he)

/-- **Malleability of multiplicative ElGamal**: the mauled encryption of `m` decrypts to `m + g`
under the matching secret key. -/
theorem elGamalDecryptDet_elGamalMaulCiphertext (d : ℕ → F.Desc) (n a b : ℕ)
    (m : F.Carrier (d n)) :
    F.elGamalDecryptDet d n (encNat a) (F.elGamalMaulCiphertext (d n)
      (encPair encBits encBits
        (F.encodeElGamalEncrypt (d n, F.encodeElGamalPublicKey (d n, a), F.encode (d n) m, b)))) =
      F.encode (d n) (m + F.generator (d n)) := by
  simp only [encodeElGamalPublicKey_eq_encode, encodeElGamalEncrypt_encode,
    elGamalMaulCiphertext_encode, elGamalDecryptDet, ofBits_encNat, unframe_encPair_encBits,
    dropFrame_encPair_encBits, decodeElGamal_encode, elGamalDecrypt, elGamalEncrypt, smul_smul,
    mul_comm (b : ZMod (F.order (d n)))]
  congr 1
  abel

/-- `elGamalMaulCiphertext` is computable in polynomial time. -/
theorem computableInPolyTime_elGamalMaulCiphertext :
    ComputableInPolyTime (fun p : F.Desc × List Bool => F.elGamalMaulCiphertext p.1 p.2)
      (encPair F.encDesc encBits) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc encBits
  have hct := ComputableInPolyTime.snd F.encDesc encBits
  have hadd := F.computableInPolyTime_add.comp
    (hd.prod ((ComputableInPolyTime.dropFrame.comp hct).prod
      (F.computableInPolyTime_generator.comp hd)))
  unfold elGamalMaulCiphertext
  fun_prop

/-- **The 1CCA malleability adversary against multiplicative ElGamal** ([BonehShoup2023],
Exercise 12.1, p. 512). Phase 1 makes no query and chooses `(msg₀ n, msg₁ n)`. Phase 2 maps the
challenge ciphertext `ct` to `elGamalMaulCiphertext (d n) ct`, queries the decryption oracle on it
once, and outputs whether the reply is the encoded decryption `some (encodeMsg (d n) (msg₁ n) + g)`
that world `1` produces. It reads only a prefix one bit longer than that target word. -/
def elGamalMaulAdversary {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc) (msg₀ msg₁ : ℕ → Msg) : CCA2AdversaryOf Msg where
  choose n _ := pure ((msg₀ n, msg₁ n), [])
  guess n _ ct := do
    let target := encOption encBits
      (some (F.add (d n, encodeMsg (d n) (msg₁ n), F.encode (d n) (F.generator (d n)))))
    let reply ← List.take (target.length + 1) <$>
      ProbOracleComp.query ((), F.elGamalMaulCiphertext (d n) ct)
    return reply == target

/-- `elGamalMaulAdversary` is strict oracle PPT whenever the group family, the message encoder
and both message choices are computable in polynomial time. -/
theorem isPPT_elGamalMaulAdversary {Msg : Type} {encMsg : Msg ↪ List Bool}
    {encodeMsg : F.Desc → Msg → List Bool} {d : ℕ → F.Desc} {msg₀ msg₁ : ℕ → Msg}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hmsg₀ : ComputableInPolyTime msg₀ encUnary encMsg)
    (hmsg₁ : ComputableInPolyTime msg₁ encUnary encMsg) :
    (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁).IsPPT encMsg where
  choose := by
    have hn := ComputableInPolyTime.fst encUnary encBits
    exact ((((hmsg₀.comp hn).prod (hmsg₁.comp hn)).prod
      (ComputableInPolyTime.const ([] : List Bool))).isOraclePPTOn).isOraclePPT
  guess := by
    let E := encGuessInput
    have hn : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.1) E encUnary := by
      fun_prop
    have hct : ComputableInPolyTime (fun p : ℕ × List Bool × List Bool => p.2.2) E encBits := by
      fun_prop
    have hdn := hd.comp hn
    have hw : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          F.add (d p.1, encodeMsg (d p.1) (msg₁ p.1), F.encode (d p.1) (F.generator (d p.1)))) E
        encBits :=
      F.computableInPolyTime_add.comp (hdn.prod ((hencMsg.comp (hdn.prod (hmsg₁.comp hn))).prod
        (F.computableInPolyTime_generator.comp hdn)))
    have htarget : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool =>
          encOption encBits (some (F.add (d p.1, encodeMsg (d p.1) (msg₁ p.1),
            F.encode (d p.1) (F.generator (d p.1)))))) E encBits := by
      fun_prop
    have hreq : ComputableInPolyTime
        (fun p : ℕ × List Bool × List Bool => F.elGamalMaulCiphertext (d p.1) p.2.2) E encBits :=
      F.computableInPolyTime_elGamalMaulCiphertext.comp (hdn.prod hct)
    have hout : ComputableInPolyTime
        (fun p : (ℕ × List Bool × List Bool) × List Bool =>
          p.2 == encOption encBits (some (F.add (d p.1.1, encodeMsg (d p.1.1) (msg₁ p.1.1),
            F.encode (d p.1.1) (F.generator (d p.1.1)))))) (encPair E encBits) encBool :=
      (ComputableInPolyTime.snd E encBits).beq (htarget.comp (ComputableInPolyTime.fst E encBits))
    exact (IsOraclePPTOn.query_take' () hreq (by fun_prop)).bind_with hout.isOraclePPTOn

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

/-- In world `bit`, if the selected message encodes `xb` and `msg₁ n` encodes `x₁`, the game
outputs `decide (xb = x₁)` with probability `1`. -/
private theorem eval_cca2GameOn_elGamalMaulAdversary_aux {Msg : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encodeMsg : F.Desc → Msg → List Bool}
    {d : ℕ → F.Desc} {msg₀ msg₁ : ℕ → Msg} {bit : Bool} {n : ℕ}
    (hvalid : ∀ u, valid n (encPair F.encDesc encBits (d n, u)) (msg₀ n) (msg₁ n) = true)
    {xb x₁ : F.Carrier (d n)}
    (hxb : encodeMsg (d n) (if bit then msg₁ n else msg₀ n) = F.encode (d n) xb)
    (hx₁ : encodeMsg (d n) (msg₁ n) = F.encode (d n) x₁) :
    ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
      (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) bit n) = PMF.pure (decide (xb = x₁)) := by
  have hmaul (a b : ℕ) :
      let ct := encPair encBits encBits
        (F.encodeElGamalEncrypt (d n, F.encodeElGamalPublicKey (d n, a), F.encode (d n) xb, b))
      (F.elGamalMaulCiphertext (d n) ct == ct) = false := by
    rw [beq_eq_false_iff_ne, encodeElGamalPublicKey_eq_encode, encodeElGamalEncrypt_encode]
    exact F.elGamalMaulCiphertext_ne (d n) _ _
  simp only [cca2GameOn, elGamalMaulAdversary, elGamalKeyGenProb, elGamalEncryptProb,
    ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.msgs, hvalid, ↓reduceIte,
    ProbComp.eval_bind, ProbComp.eval_pure, runWith_norm, pmf_norm, hxb, hx₁,
    dropFrame_encPair_encBits, cca2Phase2Oracle, F.add_encode, hmaul, Bool.false_eq_true,
    elGamalDecryptOpt, elGamalDecryptDet_elGamalMaulCiphertext, take_length_succ_beq,
    EmbeddingLike.apply_eq_iff_eq, Option.some.injEq, (F.encode_injective (d n)).eq_iff,
    add_left_inj, PMF.bind_const]

/-- **World `bit` of the 1CCA game against multiplicative ElGamal outputs `bit`**
([BonehShoup2023], Exercise 12.1, p. 512): if both challenge messages are admissible under every
honest public key and encode distinct group elements, `elGamalMaulAdversary` outputs the challenge
bit with probability `1`. -/
theorem eval_cca2GameOn_elGamalMaulAdversary {Msg : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encodeMsg : F.Desc → Msg → List Bool}
    {d : ℕ → F.Desc} {msg₀ msg₁ : ℕ → Msg} {n : ℕ}
    (hvalid : ∀ u, valid n (encPair F.encDesc encBits (d n, u)) (msg₀ n) (msg₁ n) = true)
    {x₀ x₁ : F.Carrier (d n)} (hx₀ : encodeMsg (d n) (msg₀ n) = F.encode (d n) x₀)
    (hx₁ : encodeMsg (d n) (msg₁ n) = F.encode (d n) x₁) (hne : x₀ ≠ x₁) (bit : Bool) :
    ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
      (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) bit n) = PMF.pure bit := by
  cases bit
  · rw [F.eval_cca2GameOn_elGamalMaulAdversary_aux hvalid hx₀ hx₁, decide_eq_false hne]
  · rw [F.eval_cca2GameOn_elGamalMaulAdversary_aux hvalid hx₁ hx₁, decide_eq_true rfl]

/-- **`elGamalMaulAdversary` has 1CCA advantage `1`** against multiplicative ElGamal
([BonehShoup2023], Exercise 12.1, p. 512), under the hypotheses of
`eval_cca2GameOn_elGamalMaulAdversary`. -/
theorem advantage_cca2GameOn_elGamalMaulAdversary {Msg : Type}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encodeMsg : F.Desc → Msg → List Bool}
    {d : ℕ → F.Desc} {msg₀ msg₁ : ℕ → Msg} {n : ℕ}
    (hvalid : ∀ u, valid n (encPair F.encDesc encBits (d n, u)) (msg₀ n) (msg₁ n) = true)
    {x₀ x₁ : F.Carrier (d n)} (hx₀ : encodeMsg (d n) (msg₀ n) = F.encode (d n) x₀)
    (hx₁ : encodeMsg (d n) (msg₁ n) = F.encode (d n) x₁) (hne : x₀ ≠ x₁) :
    Game.advantage
      (ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
        (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
        (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) false n))
      (ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
        (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
        (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) true n)) = 1 := by
  rw [F.eval_cca2GameOn_elGamalMaulAdversary hvalid hx₀ hx₁ hne,
    F.eval_cca2GameOn_elGamalMaulAdversary hvalid hx₀ hx₁ hne, Game.advantage_pure_false_left]
  simp [Game.succProbability]

/-- **Multiplicative ElGamal is not 1CCA secure, general form** ([BonehShoup2023], Exercise 12.1,
p. 512): for a polynomial-time group family `d` and message encoder `encodeMsg`, if polynomial-time
message choices `msg₀ msg₁` are admissible under `valid` at every honest public key and encode
distinct group elements at every parameter, then `(elGamalKeyGenProb d, elGamalEncryptProb
encodeMsg d, elGamalDecryptOpt d)` fails `Encryption.INDCCA2On valid encMsg encBits`. -/
theorem not_indcca2On_elGamalEncryptProb {Msg : Type} {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool} {encodeMsg : F.Desc → Msg → List Bool}
    {d : ℕ → F.Desc} {msg₀ msg₁ : ℕ → Msg}
    (hencMsg : ComputableInPolyTime (fun p : F.Desc × Msg => encodeMsg p.1 p.2)
      (encPair F.encDesc encMsg) encBits)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hmsg₀ : ComputableInPolyTime msg₀ encUnary encMsg)
    (hmsg₁ : ComputableInPolyTime msg₁ encUnary encMsg)
    (hvalid : ∀ n u, valid n (encPair F.encDesc encBits (d n, u)) (msg₀ n) (msg₁ n) = true)
    (hdistinct : ∀ n, ∃ x₀ x₁ : F.Carrier (d n), encodeMsg (d n) (msg₀ n) = F.encode (d n) x₀ ∧
      encodeMsg (d n) (msg₁ n) = F.encode (d n) x₁ ∧ x₀ ≠ x₁) :
    ¬ INDCCA2On valid encMsg encBits (F.elGamalKeyGenProb d) (F.elGamalEncryptProb encodeMsg d)
      (F.elGamalDecryptOpt d) := by
  intro hcca
  have hneg := hcca _ (F.isPPT_elGamalMaulAdversary hencMsg hd hmsg₀ hmsg₁)
  have hone : (fun n => Game.advantage
      (ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
        (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
        (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) false n))
      (ProbComp.eval (cca2GameOn valid encBits (F.elGamalKeyGenProb d)
        (F.elGamalEncryptProb encodeMsg d) (F.elGamalDecryptOpt d)
        (F.elGamalMaulAdversary encodeMsg d msg₀ msg₁) true n))) = fun _ => 1 := by
    funext n
    obtain ⟨x₀, x₁, hx₀, hx₁, hne⟩ := hdistinct n
    exact F.advantage_cca2GameOn_elGamalMaulAdversary (hvalid n) hx₀ hx₁ hne
  exact not_negligible_const one_ne_zero (hone ▸ hneg)

/-- **Bit ElGamal is not 1CCA secure** ([BonehShoup2023], Exercise 12.1, p. 512, for the bit
messages `0` and `g` of `encodeBit`): for every prime-order group family `F` and polynomial-time
group family `d`, the scheme `(elGamalKeyGenProb d, elGamalEncryptProb encodeBit d)`, which is
IND-CPA secure under DDH (`DDH.indcpa_elGamalBitEncryptProb`), with decryptor
`elGamalDecryptOpt d` fails `Encryption.INDCCA2Of encBool encBits`. The adversary
`elGamalMaulAdversary` with messages `false` and `true` has advantage `1` at every parameter. -/
theorem not_indcca2Of_elGamalBitEncryptProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ¬ INDCCA2Of encBool encBits (F.elGamalKeyGenProb d) (F.elGamalEncryptProb F.encodeBit d)
      (F.elGamalDecryptOpt d) :=
  F.not_indcca2On_elGamalEncryptProb F.computableInPolyTime_encodeBit hd
    (msg₀ := fun _ => false) (msg₁ := fun _ => true) (.const false) (.const true)
    (fun _ _ => rfl) fun n =>
      ⟨_, _, F.encodeBit_eq_encode_bitElement (d n) false,
        F.encodeBit_eq_encode_bitElement (d n) true,
        (F.bitElement_injective (d n)).ne Bool.false_ne_true⟩

/-- **Bit ElGamal is not CCA secure** in the interleaved multi-challenge sense of [BonehShoup2023],
Attack Game 12.1 and Definition 12.1 (pp. 467–468): by `INDCCA2InterleavedOn.indcca2On`, from
`not_indcca2Of_elGamalBitEncryptProb`. -/
theorem not_indcca2InterleavedOf_elGamalBitEncryptProb {d : ℕ → F.Desc}
    (hd : ComputableInPolyTime d encUnary F.encDesc) :
    ¬ INDCCA2InterleavedOf encBool encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb F.encodeBit d) (F.elGamalDecryptOpt d) :=
  fun h => F.not_indcca2Of_elGamalBitEncryptProb hd h.indcca2On

/-- **Group-element ElGamal is not 1CCA secure** ([BonehShoup2023], Exercise 12.1, p. 512): for a
polynomial-time group family `d` and any admissibility predicate `valid` that admits the encoded
pair `(0, g)` under every honest public key (in particular any predicate admitting all pairs of
group elements, the message space of Exercise 11.5), the scheme
`(elGamalKeyGenProb d, elGamalEncryptProb (fun _ m => m) d, elGamalDecryptOpt d)` fails
`Encryption.INDCCA2On valid encBits encBits`. -/
theorem not_indcca2On_elGamalGroupEncryptProb {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {d : ℕ → F.Desc} (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hvalid : ∀ n u, valid n (encPair F.encDesc encBits (d n, u)) (F.encode (d n) 0)
      (F.encode (d n) (F.generator (d n))) = true) :
    ¬ INDCCA2On valid encBits encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb (fun _ m => m) d) (F.elGamalDecryptOpt d) := by
  have hmsg (b : Bool) :
      ComputableInPolyTime (fun n => F.encodeBit (d n) b) encUnary encBits :=
    F.computableInPolyTime_encodeBit.comp (hd.prod (.const b))
  refine F.not_indcca2On_elGamalEncryptProb (.snd F.encDesc encBits) hd (hmsg false) (hmsg true)
    (fun n u => ?_) fun n =>
      ⟨_, _, F.encodeBit_eq_encode_bitElement (d n) false,
        F.encodeBit_eq_encode_bitElement (d n) true,
        (F.bitElement_injective (d n)).ne Bool.false_ne_true⟩
  simpa only [encodeBit_eq_encode_bitElement, bitElement, Bool.false_eq_true, ↓reduceIte] using
    hvalid n u

/-- **Group-element ElGamal is not CCA secure** in the interleaved multi-challenge sense of
[BonehShoup2023], Attack Game 12.1 and Definition 12.1 (pp. 467–468), under the hypotheses of
`not_indcca2On_elGamalGroupEncryptProb`. -/
theorem not_indcca2InterleavedOn_elGamalGroupEncryptProb
    {valid : ℕ → List Bool → List Bool → List Bool → Bool}
    {d : ℕ → F.Desc} (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hvalid : ∀ n u, valid n (encPair F.encDesc encBits (d n, u)) (F.encode (d n) 0)
      (F.encode (d n) (F.generator (d n))) = true) :
    ¬ INDCCA2InterleavedOn valid encBits encBits (F.elGamalKeyGenProb d)
      (F.elGamalEncryptProb (fun _ m => m) d) (F.elGamalDecryptOpt d) :=
  fun h => F.not_indcca2On_elGamalGroupEncryptProb hd hvalid h.indcca2On

end Cslib.Crypto.PrimeOrderGroupFamily
