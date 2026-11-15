/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Crypto.Protocols.PerfectSecrecy.Characterization
public import CslibFrontier.Probability.BitString
import CslibFrontier.Probability.BitString.List
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.Uniform

/-!
# The example Shannon ciphers of Boneh–Shoup §2.1

The example ciphers of [BonehShoup2023], v0.6, §2.1 (printed pp. 6–10) other than the one-time pad,
as information-theoretic encryption schemes `EncScheme`, with the book's verdicts on their perfect
security. Each is `EncScheme.ofPure (uniformOfFintype K) enc dec h`, the book's Shannon cipher with
a uniformly random key; its `CiphertextIndist` is the book's Definition 2.1, and
`perfectlySecret_iff_ciphertextIndist` converts it to the library's `PerfectlySecret` (the
posterior form of [KatzLindell2020], Definition 2.3). The one-time pad itself (Example 2.1,
Theorem 2.2) is `otp` with `otp_perfectlySecret`.

The cipher definitions are exposed, as `otp` is, so that the criteria of
`CslibFrontier.Crypto.Protocols.PerfectSecrecy.Characterization`, which are stated for `ofPure`,
apply to them directly. The variable-length pad's encryption `varXor` is evaluated through its
public equation `coe_varXor`.

## Main definitions

* `additiveOTP`: the additive one-time pad over a finite additive group `G` (Example 2.4).
* `variableLengthOTP`: the variable-length one-time pad with `L` key bits (Example 2.2), built from
  `varXor`, which `coe_varXor` evaluates.
* `substitutionCipher`: the substitution cipher on words of `L` symbols of a finite alphabet `α`
  with decidable equality (Example 2.3).

## Main results

* `additiveOTP_ciphertextIndist`, `additiveOTP_perfectlySecret`: Example 2.7, the additive one-time
  pad is perfectly secure, for every finite additive group.
* `variableLengthOTP_ciphertextIndist_iff`: the variable-length one-time pad is perfectly secure if
  and only if `L = 0`; `not_perfectlySecret_variableLengthOTP` is Example 2.5 for `0 < L`.
* `variableLengthOTP_ciphertextDist_map_val`, `variableLengthOTP_ciphertextDist_eq_iff`: the
  ciphertext is a uniform word of the message's length, so two messages have the same ciphertext
  law exactly when they have the same length. This is a precise form of Example 2.5's remark that
  the ciphertext leaks the length of the message and, informally, nothing else.
* `substitutionCipher_apply_eq_iff`, `not_ciphertextIndist_substitutionCipher`,
  `not_perfectlySecret_substitutionCipher`: Example 2.6, first paragraph. A ciphertext repeats a
  symbol exactly where its message does, so for `2 ≤ L` and at least two symbols the substitution
  cipher is not perfectly secure.

## Deviations from [BonehShoup2023]

* The additive one-time pad is defined over any finite additive group, commutative or not. The
  book's cipher is the case `G = ZMod n` with `n` positive, which is `additiveOTP (ZMod n)` under
  `[NeZero n]`. The book proves Example 2.7 by `N_c = 1` in Theorem 2.1 (ii), the key being
  `-m + c`; here the ciphertext law is shown uniform instead, and the test file checks the book's
  route through `ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique`.
* The book's `{0,1}^{≤L}` is the subtype `{w : List Bool // w.length ≤ L}`; `BitString.shortWords L`
  is the same set as a `Finset`. The key `{0,1}^L` is `BitString L`, and its truncation
  `k[0 .. ℓ - 1]` is `(List.ofFn k).take ℓ`.
* Example 2.5 says that the variable-length one-time pad is not perfectly secure, using messages of
  lengths 1 and 2, so it assumes `L ≥ 2` implicitly. `variableLengthOTP_ciphertextIndist_iff` is
  exact: lengths 0 and 1 already separate for `L ≥ 1`, and for `L = 0` there is one message and the
  cipher is perfectly secure. Of the book's two masses, the `0` is
  `variableLengthOTP_ciphertextDist_apply_of_length_ne`, and the test file checks the `1/2` of a
  1-bit ciphertext under a 1-bit message for every `L ≥ 1`. The mass `(2 ^ ℓ)⁻¹` of a word of any
  length `ℓ`, which the book does not state, needs an exact-mass lemma for `BitString.uniformList`
  that the library does not have, and is not stated here.
* Example 2.6 leaves `L ≥ 2` and `|Σ| ≥ 2` implicit; here they are the hypotheses `2 ≤ L` and
  `Nontrivial α`. Neither can be dropped: the test file checks that the cipher is perfectly secure
  on words of one symbol of `Bool`, and on words over `Unit`, where there is only one message. The
  book makes no positive claim for these cases, and none is stated here in general. The second
  paragraph of Example 2.6 is an informal discussion with no statement and is not formalized.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020]
-/

public section

namespace Cslib.Crypto.Protocols.PerfectSecrecy

open Cslib.Probability.PMF

universe u

/-! ### The additive one-time pad -/

section Additive

variable (G : Type u) [AddGroup G] [Fintype G]

/-- The **additive one-time pad** over a finite additive group `G`: keys, messages and ciphertexts
are elements of `G`, with `E(k, m) = m + k`, `D(k, c) = c - k` and a uniformly random key.
[BonehShoup2023], Example 2.4 (p. 7), defines it for `G = ZMod n` with `n` positive, which is
`additiveOTP (ZMod n)` under `[NeZero n]`. -/
@[expose] noncomputable def additiveOTP : EncScheme G G G :=
  .ofPure (uniformOfFintype G) (fun k m => m + k) (fun k c => c - k) fun k m => by simp

/-- Under the additive one-time pad every message has the uniform ciphertext law. -/
theorem additiveOTP_ciphertextDist_eq_uniform (m : G) :
    (additiveOTP G).ciphertextDist m = uniformOfFintype G :=
  uniformOfFintype_map_add_left m

/-- **The additive one-time pad is perfectly secure**: [BonehShoup2023], Example 2.7 (p. 10), for
every finite additive group rather than only `ZMod n`. The book's argument is `N_c = 1` in
Theorem 2.1 (ii); this proof uses that the ciphertext law is uniform. -/
theorem additiveOTP_ciphertextIndist : (additiveOTP G).CiphertextIndist := fun m₀ m₁ => by
  rw [additiveOTP_ciphertextDist_eq_uniform, additiveOTP_ciphertextDist_eq_uniform]

/-- The additive one-time pad is perfectly secret in the posterior sense of `PerfectlySecret`. -/
theorem additiveOTP_perfectlySecret : (additiveOTP G).PerfectlySecret :=
  (EncScheme.perfectlySecret_iff_ciphertextIndist _).mpr (additiveOTP_ciphertextIndist G)

end Additive

/-! ### The variable-length one-time pad -/

section VariableLength

variable (L : ℕ)

/-- Encryption and decryption of the variable-length one-time pad (this library's name): a word `w`
of at most `L` bits, of length `ℓ`, is XORed with the first `ℓ` bits of the key `k`, the book's
`k[0 .. ℓ - 1] ⊕ w`. -/
def varXor (k : BitString L) (w : {w : List Bool // w.length ≤ L}) :
    {w : List Bool // w.length ≤ L} :=
  ⟨List.zipWith Bool.xor ((List.ofFn k).take w.1.length) w.1, by
    have := w.2
    simp only [List.length_zipWith, List.length_take, List.length_ofFn]
    omega⟩

/-- The underlying word of `varXor`: the word XORed with as many leading key bits as it has. -/
theorem coe_varXor (k : BitString L) (w : {w : List Bool // w.length ≤ L}) :
    (varXor L k w).1 = List.zipWith Bool.xor ((List.ofFn k).take w.1.length) w.1 := by
  simp only [varXor]

/-- `varXor` preserves the length of a word. -/
@[simp]
theorem length_varXor (k : BitString L) (w : {w : List Bool // w.length ≤ L}) :
    (varXor L k w).1.length = w.1.length := by
  have := w.2
  simp only [coe_varXor, List.length_zipWith, List.length_take, List.length_ofFn]
  omega

/-- `varXor` with a fixed key is an involution: decryption inverts encryption. -/
@[simp]
theorem varXor_varXor (k : BitString L) (w : {w : List Bool // w.length ≤ L}) :
    varXor L k (varXor L k w) = w := by
  apply Subtype.ext
  apply List.ext_getElem
  · rw [length_varXor, length_varXor]
  · intro i h₁ h₂
    simp [varXor]

/-- The **variable-length one-time pad** of [BonehShoup2023], Example 2.2 (p. 6): the key is `L`
uniformly random bits, messages and ciphertexts are words of at most `L` bits, and a word is
encrypted and decrypted by `varXor`, XOR with as many key bits as it is long. The book's
`{0,1}^{≤L}` is the subtype `{w : List Bool // w.length ≤ L}`; `BitString.shortWords L` is the
same set as a `Finset`. -/
@[expose] noncomputable def variableLengthOTP :
    EncScheme {w : List Bool // w.length ≤ L} (BitString L) {w : List Bool // w.length ≤ L} :=
  .ofPure (uniformOfFintype (BitString L)) (varXor L) (varXor L) (varXor_varXor L)

/-- Under the variable-length one-time pad, the ciphertext of `m` is a uniformly random word of
the length of `m`. -/
theorem variableLengthOTP_ciphertextDist_map_val (m : {w : List Bool // w.length ≤ L}) :
    ((variableLengthOTP L).ciphertextDist m).map Subtype.val =
      BitString.uniformList m.1.length := by
  have hfun : (Subtype.val ∘ fun k => varXor L k m) =
      (fun pad => List.zipWith Bool.xor pad m.1) ∘ List.take m.1.length ∘ List.ofFn := rfl
  rw [variableLengthOTP, EncScheme.ciphertextDist_ofPure, PMF.map_comp, hfun, ← PMF.map_comp,
    ← PMF.map_comp]
  change ((BitString.uniformList L).map (List.take m.1.length)).map _ = _
  rw [BitString.uniformList_take m.2, BitString.uniformList_map_zipWith_xor]

/-- Two messages have the same ciphertext law under the variable-length one-time pad exactly when
they have the same length: a precise form of the remark in [BonehShoup2023], Example 2.5 (p. 9),
that the ciphertext leaks the length of the message and nothing else. -/
theorem variableLengthOTP_ciphertextDist_eq_iff (m₀ m₁ : {w : List Bool // w.length ≤ L}) :
    (variableLengthOTP L).ciphertextDist m₀ = (variableLengthOTP L).ciphertextDist m₁ ↔
      m₀.1.length = m₁.1.length := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := congrArg (PMF.map Subtype.val) h
    rw [variableLengthOTP_ciphertextDist_map_val, variableLengthOTP_ciphertextDist_map_val] at h'
    obtain ⟨w, hw⟩ := (BitString.uniformList m₀.1.length).support_nonempty
    have h₀ := BitString.length_of_mem_support_uniformList hw
    rw [h'] at hw
    exact h₀.symm.trans (BitString.length_of_mem_support_uniformList hw)
  · apply map_injective Subtype.val_injective
    rw [variableLengthOTP_ciphertextDist_map_val, variableLengthOTP_ciphertextDist_map_val, h]

/-- Under the variable-length one-time pad a ciphertext whose length differs from the message's
has probability `0`: the mass `Pr[E(k, m₁) = c] = 0` for a 2-bit `m₁` and a 1-bit `c` in
[BonehShoup2023], Example 2.5 (p. 9). -/
theorem variableLengthOTP_ciphertextDist_apply_of_length_ne {L : ℕ}
    {m c : {w : List Bool // w.length ≤ L}} (h : c.1.length ≠ m.1.length) :
    (variableLengthOTP L).ciphertextDist m c = 0 := by
  rw [← map_apply_of_injective _ Subtype.val_injective, variableLengthOTP_ciphertextDist_map_val,
    PMF.apply_eq_zero_iff]
  exact fun hc => h (BitString.length_of_mem_support_uniformList hc)

/-- **The variable-length one-time pad is perfectly secure only without key bits**: it satisfies
Definition 2.1 of [BonehShoup2023] if and only if `L = 0`. For `L ≥ 1` the empty word and a 1-bit
word have different ciphertext laws; for `L = 0` the empty word is the only message.
[BonehShoup2023], Example 2.5 (p. 9), separates messages of lengths 1 and 2, which needs
`L ≥ 2`. -/
theorem variableLengthOTP_ciphertextIndist_iff :
    (variableLengthOTP L).CiphertextIndist ↔ L = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra hL
    have := (variableLengthOTP_ciphertextDist_eq_iff L ⟨[], Nat.zero_le _⟩
      ⟨[true], Nat.pos_of_ne_zero hL⟩).mp (h _ _)
    simp at this
  · rintro rfl m₀ m₁
    rw [variableLengthOTP_ciphertextDist_eq_iff]
    have h₀ := m₀.2
    have h₁ := m₁.2
    omega

/-- **The variable-length one-time pad is not perfectly secret** when `0 < L`: [BonehShoup2023],
Example 2.5 (p. 9), for the library's `PerfectlySecret`, with `0 < L` in place of the book's
implicit `L ≥ 2`. -/
theorem not_perfectlySecret_variableLengthOTP {L : ℕ} (hL : 0 < L) :
    ¬ (variableLengthOTP L).PerfectlySecret := by
  rw [EncScheme.perfectlySecret_iff_ciphertextIndist, variableLengthOTP_ciphertextIndist_iff]
  omega

end VariableLength

/-! ### The substitution cipher -/

section Substitution

variable (α : Type u) [Fintype α] [DecidableEq α] (L : ℕ)

/-- The **substitution cipher** of [BonehShoup2023], Example 2.3 (p. 7), over a finite alphabet
`α` with decidable equality (the book's `Σ`): messages and ciphertexts are words `Fin L → α` of
`L` symbols, the key is a uniformly random permutation of `α`, encryption applies it to each symbol
and decryption applies its inverse. -/
@[expose] noncomputable def substitutionCipher : EncScheme (Fin L → α) (Equiv.Perm α) (Fin L → α) :=
  .ofPure (uniformOfFintype (Equiv.Perm α)) (fun k m => k ∘ m) (fun k c => k.symm ∘ c)
    fun k m => by funext i; simp

variable {α L}

/-- Under the substitution cipher, every possible ciphertext of `m` repeats a symbol exactly where
`m` does. This is the observation of [BonehShoup2023], Example 2.6 (p. 10). -/
theorem substitutionCipher_apply_eq_iff {m c : Fin L → α}
    (hc : c ∈ ((substitutionCipher α L).ciphertextDist m).support) (i j : Fin L) :
    c i = c j ↔ m i = m j := by
  rw [substitutionCipher, EncScheme.ciphertextDist_ofPure, PMF.mem_support_map_iff] at hc
  obtain ⟨k, -, rfl⟩ := hc
  simp

/-- **The substitution cipher is not perfectly secure**: [BonehShoup2023], Example 2.6, first
paragraph (p. 10), with the book's implicit `L ≥ 2` and `|Σ| ≥ 2` as hypotheses. As in the book, a
message with equal first two symbols and one with different first two symbols have different
ciphertext laws. -/
theorem not_ciphertextIndist_substitutionCipher [Nontrivial α] (hL : 2 ≤ L) :
    ¬ (substitutionCipher α L).CiphertextIndist := by
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne α
  let i₀ : Fin L := ⟨0, by omega⟩
  let i₁ : Fin L := ⟨1, by omega⟩
  let m₀ : Fin L → α := fun _ => a
  let m₁ : Fin L → α := fun i => if i = i₀ then a else b
  have hc : m₀ ∈ ((substitutionCipher α L).ciphertextDist m₀).support := by
    rw [substitutionCipher, EncScheme.ciphertextDist_ofPure, PMF.mem_support_map_iff]
    exact ⟨1, by simp [uniformOfFintype_apply], rfl⟩
  rw [h m₀ m₁] at hc
  have hne : i₁ ≠ i₀ := by simp [i₀, i₁, Fin.ext_iff]
  exact hab (by simpa [m₁, hne] using (substitutionCipher_apply_eq_iff hc i₀ i₁).mp rfl)

/-- The substitution cipher is not perfectly secret in the posterior sense of `PerfectlySecret`,
for `2 ≤ L` and at least two symbols. -/
theorem not_perfectlySecret_substitutionCipher [Nontrivial α] (hL : 2 ≤ L) :
    ¬ (substitutionCipher α L).PerfectlySecret := by
  rw [EncScheme.perfectlySecret_iff_ciphertextIndist]
  exact not_ciphertextIndist_substitutionCipher hL

end Substitution

end Cslib.Crypto.Protocols.PerfectSecrecy
