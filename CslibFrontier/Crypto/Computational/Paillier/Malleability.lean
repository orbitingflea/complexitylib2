/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Paillier.Security
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Malleability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Tactic.PolyTime

/-!
# Paillier encryption is not CCA secure

Paillier encryption ([KatzLindell2020], Construction 15.11) encrypts `m` under the public key `N`
as `(1 + N) ^ m * r ^ N mod N ^ 2`. It is IND-CPA secure under decisional composite residuosity
(`DCR.indcpaOn_paillier`), but it is additively homomorphic: multiplying a ciphertext by
`1 + N`, the randomness-free encryption of `1`, adds `1` to its plaintext. Hence it is not CCA
secure: `incrementAdversary` chooses `(0, 1)`, asks the Phase 2 oracle to decrypt
`ct * (1 + N) mod N ^ 2`, which differs from the challenge `ct` because its decryption differs, and
outputs whether the reply is `2 mod N`. This is the generic argument of [BonehShoup2023],
Section 12.2.1 (pp. 469–470), instantiated through `Encryption.not_indcca2On_of_maulAdversary`; it
has 1CCA advantage exactly `1` at every security parameter and needs no assumption.

The CCA games use `decryptOpt`, the never-rejecting decryption `some ∘ decrypt`, as the scheme's
`Option`-valued decryptor, and the admissibility predicate `validMessages` of
`DCR.indcpaOn_paillier`.

## Main definitions

* `Cslib.Crypto.Paillier.decryptOpt`: decryption as the `Option`-valued CCA decryptor.
* `Cslib.Crypto.Paillier.incrementCiphertext`: multiplication of a ciphertext by `1 + N`.
* `Cslib.Crypto.Paillier.incrementAdversary`: the one-query 1CCA adversary.

## Main results

* `Cslib.Crypto.Paillier.computableInPolyTime_incrementCiphertext`,
  `Cslib.Crypto.Paillier.decrypt_incrementCiphertext`: the increment is polynomial-time and adds
  `1` modulo `N` to the plaintext of every honest ciphertext.
* `Cslib.Crypto.Paillier.isPPT_incrementAdversary`: the adversary is strict oracle PPT.
* `Cslib.Crypto.Paillier.advantage_cca2GameOn_incrementAdversary`: its advantage is `1`.
* `Cslib.Crypto.Paillier.not_indcca2On_paillier`,
  `Cslib.Crypto.Paillier.not_indcca2InterleavedOn_paillier`: Paillier is neither 1CCA secure nor
  CCA secure in the interleaved sense of [BonehShoup2023], Attack Game 12.1 and Definition 12.1.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Construction 15.11 (locator as cited in `CslibFrontier/Crypto/Computational/Paillier.lean`).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.13 (pp. 461–462, the additive homomorphism),
  Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2, pp. 467–468) and Section 12.2.1
  (pp. 469–470).
-/

public section

namespace Cslib.Crypto.Paillier

open Probability Turing.MultiTapeTM Encryption BalancedModulus

/-- Paillier decryption as the `Option`-valued decryptor of the CCA games: it never rejects and
returns `decrypt sk ct`. -/
@[expose] def decryptOpt (_n : ℕ) (sk ct : List Bool) : Option (List Bool) :=
  some (decrypt sk ct)

/-- Multiply a ciphertext by `1 + N` modulo `N ^ 2`, for the public key `pk = N`
(`addCiphertexts pk ct (encNat (1 + N))`), which adds `1` to the plaintext. -/
@[expose] def incrementCiphertext (pk ct : List Bool) : List Bool :=
  addCiphertexts pk ct (encNat (1 + ofBits pk))

/-- `incrementCiphertext` is computable in polynomial time. -/
theorem computableInPolyTime_incrementCiphertext :
    ComputableInPolyTime (fun ⟨pk, ct⟩ => incrementCiphertext pk ct) (encPair encBits encBits)
      encBits := by
  unfold incrementCiphertext addCiphertexts
  fun_prop

/-- **Incrementing adds one to the plaintext**: for a valid description `d`, every ciphertext in
the support of `encrypt n (encNat N) m` increments to a ciphertext that decrypts to
`(m + 1) mod N`. -/
theorem decrypt_incrementCiphertext (d : Desc) {n m : ℕ} {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encNat d.modulus) m)).support) :
    decrypt (encPair encNat encNat (d.modulus, d.totient))
        (incrementCiphertext (encNat d.modulus) ct) =
      encNat ((m + 1) % d.modulus) := by
  obtain ⟨r, hr, rfl⟩ := exists_of_mem_support_encrypt hct
  have hN : d.modulus ≠ 0 := NeZero.ne _
  have hc : ((ciphertext d.modulus m r * (1 + d.modulus) % d.modulus ^ 2 : ℕ) :
      ZMod (d.modulus ^ 2)) =
      (1 + d.modulus) ^ (m + 1) * (r : ZMod (d.modulus ^ 2)) ^ d.modulus := by
    rw [ZMod.natCast_mod, Nat.cast_mul, natCast_ciphertext hN]
    push_cast
    ring
  rw [incrementCiphertext, addCiphertexts, ofBits_encNat, ofBits_encNat, ofBits_encNat, decrypt,
    unframe_encPair, dropFrame_encPair, ofBits_encNat, ofBits_encNat, ofBits_encNat, d.totient_eq,
    decryptNat_eq d.one_lt_modulus d.coprime_totient hr hc]

/-- **The 1CCA increment adversary against Paillier**: choose `(0, 1)`, query the decryption
oracle on `incrementCiphertext pk ct`, and output whether the reply is `some (2 mod N)`, which
happens exactly when the challenge encrypts `1`. -/
def incrementAdversary : CCA2AdversaryOf ℕ :=
  maulAdversary (fun _ _ => 0) (fun _ _ => 1) (fun _ pk ct => incrementCiphertext pk ct)
    (fun _ pk => encOption encBits (some (encNat (2 % ofBits pk))))

/-- The target reply `some (2 mod N)` of `incrementAdversary` is polynomial-time. -/
private theorem computableInPolyTime_incrementTarget :
    ComputableInPolyTime (fun ⟨_, pk⟩ => encOption encBits (some (encNat (2 % ofBits pk))))
      (encPair encUnary encBits) encBits := by
  have hN := ComputableInPolyTime.bitsToNat.comp (ComputableInPolyTime.snd encUnary encBits)
  have h2 := (ComputableInPolyTime.binary_mod' (ComputableInPolyTime.const 2) hN).encoding_comp
  fun_prop

/-- `incrementAdversary` is strict oracle PPT. -/
theorem isPPT_incrementAdversary : incrementAdversary.IsPPT encNat :=
  isPPT_maulAdversary (.const 0) (.const 1)
    (computableInPolyTime_incrementCiphertext.comp (by fun_prop))
    computableInPolyTime_incrementTarget

/-- The challenge pair `(0, 1)` of `incrementAdversary` is admissible under every honest public
key. -/
private theorem validMessages_keyGen {gen : ℕ → ProbComp Desc} {n : ℕ}
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support) :
    validMessages n keys.1 0 1 = true := by
  obtain ⟨d, rfl⟩ := exists_of_mem_support_keyGen hkeys
  simp only [validMessages, ofBits_encNat, decide_eq_true_eq]
  exact ⟨by have := d.one_lt_modulus; omega, d.one_lt_modulus⟩

/-- The malleability conditions of `incrementAdversary` on every honest key pair. -/
private theorem increment_conditions {gen : ℕ → ProbComp Desc} {n : ℕ} (bit : Bool)
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support)
    {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then 1 else 0))).support) :
    decryptOpt n keys.2 (incrementCiphertext keys.1 ct) ≠ decryptOpt n keys.2 ct ∧
      (encOption encBits (decryptOpt n keys.2 (incrementCiphertext keys.1 ct)) =
        encOption encBits (some (encNat (2 % ofBits keys.1))) ↔ bit = true) := by
  obtain ⟨d, hkeq⟩ := exists_of_mem_support_keyGen hkeys
  have hN := d.one_lt_modulus
  have hm : (if bit then 1 else 0) < ofBits keys.1 := by
    rw [hkeq, ofBits_encNat]; cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hcorrect := decrypt_encrypt hkeys hm hct
  subst hkeq
  have h2 : 2 % d.modulus ≠ 1 := by
    rcases Nat.lt_or_ge 2 d.modulus with h | h
    · rw [Nat.mod_eq_of_lt h]; omega
    · obtain h' : d.modulus = 2 := by omega
      rw [h']; decide
  dsimp only at hcorrect ⊢
  simp only [decryptOpt, decrypt_incrementCiphertext d hct, hcorrect, ofBits_encNat, ne_eq,
    Option.some.injEq, EmbeddingLike.apply_eq_iff_eq]
  cases bit
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add, Nat.mod_eq_of_lt hN, one_ne_zero,
      not_false_eq_true, iff_false, true_and]
    exact fun h => h2 h.symm
  · simp only [↓reduceIte, Nat.reduceAdd, and_true]
    exact h2

/-- `incrementAdversary` has 1CCA advantage exactly `1` against Paillier under `validMessages`. -/
theorem advantage_cca2GameOn_incrementAdversary (gen : ℕ → ProbComp Desc) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2GameOn validMessages encBits (keyGen gen) encrypt decryptOpt
        incrementAdversary false n))
      (ProbComp.eval (cca2GameOn validMessages encBits (keyGen gen) encrypt decryptOpt
        incrementAdversary true n)) = 1 := by
  unfold incrementAdversary
  exact advantage_cca2GameOn_maulAdversary (fun _ hkeys => validMessages_keyGen hkeys)
    fun bit _ hkeys _ hct => increment_conditions bit hkeys hct

/-- **Paillier encryption is not 1CCA secure** ([BonehShoup2023], Section 12.2.1, pp. 469–470,
applied to the additive homomorphism of Paillier encryption): for every modulus generator `gen`,
the scheme `(keyGen gen, encrypt)` of `DCR.indcpaOn_paillier`, with decryptor `decryptOpt`, fails
`Encryption.INDCCA2On validMessages encNat encBits`. No assumption is needed; so under DCR (and
`hsize`) Paillier is IND-CPA but not IND-CCA2. -/
theorem not_indcca2On_paillier (gen : ℕ → ProbComp Desc) :
    ¬ INDCCA2On validMessages encNat encBits (keyGen gen) encrypt decryptOpt :=
  not_indcca2On_of_maulAdversary (msg₀ := fun _ _ => 0) (msg₁ := fun _ _ => 1)
    (maul := fun _ pk ct => incrementCiphertext pk ct)
    (target := fun _ pk => encOption encBits (some (encNat (2 % ofBits pk))))
    (.const 0) (.const 1) (computableInPolyTime_incrementCiphertext.comp (by fun_prop))
    computableInPolyTime_incrementTarget (fun _ _ hkeys => validMessages_keyGen hkeys)
    fun _ bit _ hkeys _ hct => increment_conditions bit hkeys hct

/-- **Paillier encryption is not CCA secure** in the interleaved multi-challenge sense of
[BonehShoup2023], Attack Game 12.1 and Definition 12.1 (pp. 467–468), by
`INDCCA2InterleavedOn.indcca2On`. -/
theorem not_indcca2InterleavedOn_paillier (gen : ℕ → ProbComp Desc) :
    ¬ INDCCA2InterleavedOn validMessages encNat encBits (keyGen gen) encrypt decryptOpt :=
  fun h => not_indcca2On_paillier gen h.indcca2On

end Cslib.Crypto.Paillier
