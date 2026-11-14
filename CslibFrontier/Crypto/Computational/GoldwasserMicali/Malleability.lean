/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GoldwasserMicali
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved
public import CslibFrontier.Crypto.Computational.Encryption.CCA.Malleability
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.WordsRoundTrip
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Tactic.PolyTime

/-!
# Goldwasser–Micali encryption is not CCA secure

Goldwasser–Micali encryption ([KatzLindell2020], Construction 15.28) encrypts a bit `m` under the
public key `⟨N, z⟩` as `z ^ m * r ^ 2 mod N`. It is IND-CPA secure under quadratic residuosity
(`indcpa_blumGoldwasserMicali` for the Blum-modulus variant), but multiplying a ciphertext by the
public nonresidue `z` flips its plaintext (the XOR homomorphism of [KatzLindell2020],
Exercise 15.11, `decrypt_mulCiphertexts`). Hence it is not CCA secure: `flipAdversary` asks the
Phase 2 oracle to decrypt `ct * z mod N`, which differs from the challenge `ct` because its
decryption differs, and outputs the negation of the reply. This is the generic argument of
[BonehShoup2023], Section 12.2.1 (pp. 469–470), instantiated through
`Encryption.not_indcca2On_of_maulAdversary`; it has 1CCA advantage exactly `1` at every security
parameter and needs no assumption.

The CCA games use `decryptOpt`, the never-rejecting decryption `some ∘ decrypt`, as the scheme's
`Option`-valued decryptor. Both key generators of
`CslibFrontier/Crypto/Computational/GoldwasserMicali.lean` are covered: `keyGen gen` over any
generator of valid key descriptions, unconditionally, and `blumKeyGen gen` with public nonresidue
`-1`, the scheme of `indcpa_blumGoldwasserMicali`, under that theorem's own Blum-modulus condition
`hblum`, which makes `-1` a nonresidue and decryption correct.

## Main definitions

* `Cslib.Crypto.GoldwasserMicali.decryptOpt`: decryption as the `Option`-valued CCA decryptor.
* `Cslib.Crypto.GoldwasserMicali.flipCiphertext`: multiplication of a ciphertext by the public
  nonresidue.
* `Cslib.Crypto.GoldwasserMicali.flipAdversary`: the one-query 1CCA adversary.

## Main results

* `Cslib.Crypto.GoldwasserMicali.computableInPolyTime_flipCiphertext`,
  `Cslib.Crypto.GoldwasserMicali.KeyDesc.decrypt_flipCiphertext`: the flip is polynomial-time and
  negates the plaintext of every honest ciphertext.
* `Cslib.Crypto.GoldwasserMicali.isPPT_flipAdversary`: the adversary is strict oracle PPT.
* `Cslib.Crypto.GoldwasserMicali.advantage_cca2Game_flipAdversary`,
  `Cslib.Crypto.GoldwasserMicali.advantage_cca2Game_blum_flipAdversary`: its advantage is `1`.
* `Cslib.Crypto.GoldwasserMicali.not_indcca2_goldwasserMicali`,
  `Cslib.Crypto.GoldwasserMicali.not_indcca2_blumGoldwasserMicali`,
  `Cslib.Crypto.GoldwasserMicali.not_indcca2Interleaved_goldwasserMicali`,
  `Cslib.Crypto.GoldwasserMicali.not_indcca2Interleaved_blumGoldwasserMicali`:
  Goldwasser–Micali is neither 1CCA secure nor CCA secure in the interleaved sense of
  [BonehShoup2023], Attack Game 12.1 and Definition 12.1.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Construction 15.28 and Exercise 15.11 (locators as cited in
  `CslibFrontier/Crypto/Computational/GoldwasserMicali.lean`).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2,
  pp. 467–468) and Section 12.2.1 (pp. 469–470).
-/

public section

namespace Cslib.Crypto.GoldwasserMicali

open Probability Turing.MultiTapeTM Encryption

/-- Goldwasser–Micali decryption as the `Option`-valued decryptor of the CCA games: it never
rejects and returns `decrypt sk ct`. -/
@[expose] def decryptOpt (_n : ℕ) (sk ct : List Bool) : Option Bool :=
  some (decrypt sk ct)

/-- Multiply a ciphertext by the public nonresidue `z` of `pk = ⟨N, z⟩`, modulo `N`
(`mulCiphertexts pk ct (encNat z)`), which flips the plaintext. -/
@[expose] def flipCiphertext (pk ct : List Bool) : List Bool :=
  mulCiphertexts pk ct (dropFrame pk)

/-- `flipCiphertext` is computable in polynomial time. -/
theorem computableInPolyTime_flipCiphertext :
    ComputableInPolyTime (fun ⟨pk, ct⟩ => flipCiphertext pk ct) (encPair encBits encBits)
      encBits := by
  have hpk := ComputableInPolyTime.fst encBits encBits
  have hct := ComputableInPolyTime.snd encBits encBits
  exact computableInPolyTime_mulCiphertexts.comp
    (hpk.prod (hct.prod (ComputableInPolyTime.dropFrame.comp hpk)))

/-- **Flipping negates the plaintext**: for a valid key description `k`, every ciphertext in the
support of `encrypt n ⟨N, z⟩ m` flips to a ciphertext that decrypts to `!m`. -/
theorem KeyDesc.decrypt_flipCiphertext (k : KeyDesc) {n : ℕ} {m : Bool} {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encPair encNat encNat (k.modulus, k.z)) m)).support) :
    decrypt (encPair encNat encNat (k.p, k.q))
      (flipCiphertext (encPair encNat encNat (k.modulus, k.z)) ct) = !m := by
  obtain ⟨r, hr, rfl⟩ := exists_of_mem_support_encrypt rfl hct
  have hz : ciphertext k.modulus k.z true 1 = k.z := by
    simp only [ciphertext, powMod_of_ne_zero (NeZero.ne k.modulus), one_pow,
      Nat.one_mod_eq_one.mpr k.one_lt_modulus.ne', mul_one, ↓reduceIte,
      Nat.mod_eq_of_lt k.z_lt_modulus]
  have hmul : mulCiphertextsNat k.modulus (ciphertext k.modulus k.z m r) k.z =
      ciphertext k.modulus k.z (m ^^ true) ((if m && true then k.z else 1) * r * 1) := by
    rw [← mulCiphertextsNat_ciphertext (NeZero.ne k.modulus), hz]
  have hr' : ((if m && true then k.z else 1) * r * 1).Coprime k.modulus := by
    rw [mul_one]
    exact Nat.Coprime.mul_left (by cases m; exacts [Nat.coprime_one_left _, k.coprime_z]) hr
  rw [flipCiphertext, mulCiphertexts, dropFrame_encPair, unframe_encPair, ofBits_encNat,
    ofBits_encNat, ofBits_encNat, hmul, decrypt, unframe_encPair, dropFrame_encPair,
    ofBits_encNat, ofBits_encNat, ofBits_encNat,
    k.decryptNat_ciphertext hr', Bool.xor_true]

/-- **The 1CCA flipping adversary against Goldwasser–Micali**: choose `(false, true)`, query the
decryption oracle on `flipCiphertext pk ct`, and output whether the reply is `some false`, which
happens exactly when the challenge encrypts `true`. -/
def flipAdversary : CCA2Adversary :=
  maulAdversary (fun _ _ => false) (fun _ _ => true) (fun _ pk ct => flipCiphertext pk ct)
    (fun _ _ => encOption encBool (some false))

/-- `flipAdversary` is strict oracle PPT. -/
theorem isPPT_flipAdversary : flipAdversary.IsPPT :=
  isPPT_maulAdversary (.const false) (.const true)
    (computableInPolyTime_flipCiphertext.comp (by fun_prop)) (.const _)

/-- On a valid key description, flipping changes the decryption of an honest encryption of `m`,
and the decryption of the flipped ciphertext is `some false` exactly when `m = true`. -/
private theorem KeyDesc.flip_conditions (k : KeyDesc) {n : ℕ} {m : Bool} {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n (encPair encNat encNat (k.modulus, k.z)) m)).support) :
    decryptOpt n (encPair encNat encNat (k.p, k.q))
        (flipCiphertext (encPair encNat encNat (k.modulus, k.z)) ct) ≠
      decryptOpt n (encPair encNat encNat (k.p, k.q)) ct ∧
    (encOption encBool (decryptOpt n (encPair encNat encNat (k.p, k.q))
        (flipCiphertext (encPair encNat encNat (k.modulus, k.z)) ct)) =
      encOption encBool (some false) ↔ m = true) := by
  simp only [decryptOpt, k.decrypt_flipCiphertext hct, k.decrypt_encrypt m hct, ne_eq,
    Option.some.injEq, EmbeddingLike.apply_eq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_false]
  cases m <;> decide

/-- The malleability conditions of `flipAdversary` on every honest key pair of `keyGen gen`. -/
private theorem flip_conditions_keyGen (gen : ℕ → ProbComp KeyDesc) (n : ℕ) (bit : Bool)
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (keyGen gen n)).support)
    {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then true else false))).support) :
    decryptOpt n keys.2 (flipCiphertext keys.1 ct) ≠ decryptOpt n keys.2 ct ∧
      (encOption encBool (decryptOpt n keys.2 (flipCiphertext keys.1 ct)) =
        encOption encBool (some false) ↔ bit = true) := by
  obtain ⟨k, rfl⟩ := exists_of_mem_support_keyGen hkeys
  exact k.flip_conditions (by cases bit <;> simpa only [Bool.false_eq_true, ↓reduceIte] using hct)

/-- The malleability conditions of `flipAdversary` on every honest key pair of `blumKeyGen gen`
when `gen n` draws Blum moduli. -/
private theorem flip_conditions_blumKeyGen {gen : ℕ → ProbComp ModulusDesc} {n : ℕ}
    (hblum : ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q) (bit : Bool)
    {keys : List Bool × List Bool} (hkeys : keys ∈ (ProbComp.eval (blumKeyGen gen n)).support)
    {ct : List Bool}
    (hct : ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then true else false))).support) :
    decryptOpt n keys.2 (flipCiphertext keys.1 ct) ≠ decryptOpt n keys.2 ct ∧
      (encOption encBool (decryptOpt n keys.2 (flipCiphertext keys.1 ct)) =
        encOption encBool (some false) ↔ bit = true) := by
  simp only [blumKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
    PMF.support_pure, Set.mem_singleton_iff] at hkeys
  obtain ⟨d, hd, rfl⟩ := hkeys
  let k := KeyDesc.ofBlum d (hblum d hd)
  have hpk : blumPublicKey (d.p * d.q) = encPair encNat encNat (k.modulus, k.z) := by
    rw [blumPublicKey]; rfl
  have hsk : encPair encNat encNat (d.p, d.q) = encPair encNat encNat (k.p, k.q) := rfl
  dsimp only at hct ⊢
  rw [hpk] at hct ⊢
  rw [hsk]
  exact k.flip_conditions (by cases bit <;> simpa only [Bool.false_eq_true, ↓reduceIte] using hct)

/-- `flipAdversary` has 1CCA advantage exactly `1` against Goldwasser–Micali over any generator
of valid key descriptions. -/
theorem advantage_cca2Game_flipAdversary (gen : ℕ → ProbComp KeyDesc) (n : ℕ) :
    Game.advantage
      (ProbComp.eval (cca2Game encBool (keyGen gen) encrypt decryptOpt flipAdversary false n))
      (ProbComp.eval (cca2Game encBool (keyGen gen) encrypt decryptOpt flipAdversary true n)) =
      1 := by
  unfold flipAdversary
  exact advantage_cca2GameOn_maulAdversary (fun _ _ => rfl) fun bit _ hkeys _ hct =>
    flip_conditions_keyGen gen n bit hkeys hct

/-- `flipAdversary` has 1CCA advantage exactly `1` against Blum-modulus Goldwasser–Micali whenever
`gen n` draws Blum moduli. -/
theorem advantage_cca2Game_blum_flipAdversary {gen : ℕ → ProbComp ModulusDesc} {n : ℕ}
    (hblum : ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q) :
    Game.advantage
      (ProbComp.eval (cca2Game encBool (blumKeyGen gen) encrypt decryptOpt flipAdversary false n))
      (ProbComp.eval (cca2Game encBool (blumKeyGen gen) encrypt decryptOpt flipAdversary true n)) =
      1 := by
  unfold flipAdversary
  exact advantage_cca2GameOn_maulAdversary (fun _ _ => rfl) fun bit _ hkeys _ hct =>
    flip_conditions_blumKeyGen hblum bit hkeys hct

/-- `flipAdversary` refutes `Encryption.INDCCA2` for any key generator on whose honest key pairs
the flip conditions hold. -/
private theorem not_indcca2_of_flip_conditions {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    (h : ∀ n bit, ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ ct ∈ (ProbComp.eval (encrypt n keys.1 (if bit then true else false))).support,
        decryptOpt n keys.2 (flipCiphertext keys.1 ct) ≠ decryptOpt n keys.2 ct ∧
          (encOption encBool (decryptOpt n keys.2 (flipCiphertext keys.1 ct)) =
            encOption encBool (some false) ↔ bit = true)) :
    ¬ INDCCA2 keyGen encrypt decryptOpt :=
  not_indcca2On_of_maulAdversary (msg₀ := fun _ _ => false) (msg₁ := fun _ _ => true)
    (maul := fun _ pk ct => flipCiphertext pk ct)
    (target := fun _ _ => encOption encBool (some false))
    (.const false) (.const true) (computableInPolyTime_flipCiphertext.comp (by fun_prop))
    (.const _) (fun _ _ _ => rfl) h

/-- **Goldwasser–Micali encryption is not 1CCA secure** ([BonehShoup2023], Section 12.2.1,
pp. 469–470, applied to the XOR homomorphism of [KatzLindell2020], Exercise 15.11): for every
generator `gen` of valid key descriptions, `(keyGen gen, encrypt, decryptOpt)` fails
`Encryption.INDCCA2`. No assumption is needed; `flipAdversary` has advantage `1`. -/
theorem not_indcca2_goldwasserMicali (gen : ℕ → ProbComp KeyDesc) :
    ¬ INDCCA2 (keyGen gen) encrypt decryptOpt :=
  not_indcca2_of_flip_conditions fun n bit _ hkeys _ hct =>
    flip_conditions_keyGen gen n bit hkeys hct

/-- **Blum-modulus Goldwasser–Micali is not 1CCA secure**: the scheme
`(blumKeyGen gen, encrypt)` of `indcpa_blumGoldwasserMicali`, with decryptor `decryptOpt`, fails
`Encryption.INDCCA2` under that theorem's own Blum-modulus condition, with no hardness assumption.
So under quadratic residuosity (and `hsize`) it is IND-CPA but not IND-CCA2. -/
theorem not_indcca2_blumGoldwasserMicali {gen : ℕ → ProbComp ModulusDesc}
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q) :
    ¬ INDCCA2 (blumKeyGen gen) encrypt decryptOpt :=
  not_indcca2_of_flip_conditions fun n bit _ hkeys _ hct =>
    flip_conditions_blumKeyGen (hblum n) bit hkeys hct

/-- **Goldwasser–Micali encryption is not CCA secure** in the interleaved multi-challenge sense of
[BonehShoup2023], Attack Game 12.1 and Definition 12.1 (pp. 467–468), by
`INDCCA2InterleavedOn.indcca2On`. -/
theorem not_indcca2Interleaved_goldwasserMicali (gen : ℕ → ProbComp KeyDesc) :
    ¬ INDCCA2Interleaved (keyGen gen) encrypt decryptOpt :=
  fun h => not_indcca2_goldwasserMicali gen h.indcca2On

/-- **Blum-modulus Goldwasser–Micali is not CCA secure** in the interleaved multi-challenge sense
of [BonehShoup2023], Attack Game 12.1 and Definition 12.1 (pp. 467–468). -/
theorem not_indcca2Interleaved_blumGoldwasserMicali {gen : ℕ → ProbComp ModulusDesc}
    (hblum : ∀ n, ∀ d ∈ (ProbComp.eval (gen n)).support, IsBlumModulus d.p d.q) :
    ¬ INDCCA2Interleaved (blumKeyGen gen) encrypt decryptOpt :=
  fun h => not_indcca2_blumGoldwasserMicali hblum h.indcca2On

end Cslib.Crypto.GoldwasserMicali
