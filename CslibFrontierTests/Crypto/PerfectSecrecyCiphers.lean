/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers
import CslibFrontier.Probability.PMF.Map
import Mathlib.Data.ZMod.Defs

/-!
# The example ciphers of Boneh–Shoup §2.1: checked instances

Checks for `CslibFrontier.Crypto.Protocols.PerfectSecrecy.ShannonCiphers`, the example ciphers of
[BonehShoup2023] §2.1. The file is a `module` client with ordinary imports, and applies every
public theorem of that module.

* The additive one-time pad over `ZMod 6` gives every ciphertext mass `1/6`, and is perfectly
  secure, both through the uniform ciphertext law and through the book's route, `N_c = 1` with the
  key `-m + c`.
* The variable-length one-time pad evaluates on a concrete key and word, and decrypts what it
  encrypts. With at least one key bit, a 1-bit ciphertext has mass `1/2` under a 1-bit message,
  and with two key bits it has mass `0` under a 2-bit message, the two numbers of Example 2.5;
  messages of different lengths have different ciphertext laws. With no key bits it is perfectly
  secure, so `0 < L` is needed.
* The substitution cipher never sends `00` to `01`, and on two symbols of a three-letter alphabet
  it is not perfectly secure. On one symbol of `Bool`, and on two symbols of `Unit`, it is, so both
  `2 ≤ L` and `Nontrivial α` are needed.
-/

namespace CslibFrontierTests.Crypto.PerfectSecrecyCiphers

open Cslib Cslib.Probability.PMF Cslib.Crypto.Protocols.PerfectSecrecy

/-! ### The additive one-time pad -/

/-- Over `ZMod 6` every ciphertext has probability `1/6`, whatever the message. -/
example (m c : ZMod 6) : (additiveOTP (ZMod 6)).ciphertextDist m c = 1 / 6 := by
  rw [additiveOTP_ciphertextDist_eq_uniform, uniformOfFintype_apply, ZMod.card, one_div,
    Nat.cast_ofNat]

/-- The additive one-time pad over `ZMod 6`, the book's case `n = 6`, satisfies Definition 2.1. -/
example : (additiveOTP (ZMod 6)).CiphertextIndist :=
  additiveOTP_ciphertextIndist _

/-- The additive one-time pad over `ZMod 6` is perfectly secret. -/
public theorem additiveOTP_zmod_six_perfectlySecret : (additiveOTP (ZMod 6)).PerfectlySecret :=
  additiveOTP_perfectlySecret _

/-- The book's proof of Example 2.7: each message and ciphertext have exactly one key, `-m + c`. -/
example : (additiveOTP (ZMod 6)).CiphertextIndist :=
  EncScheme.ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique _ _ _ fun m c =>
    ⟨-m + c, by simp, fun k hk => by rw [← hk]; simp⟩

/-! ### The variable-length one-time pad -/

/-- Key `101`, word `11`: the word is XORed with the first two key bits, giving `01`. -/
example : (varXor 3 ![true, false, true] ⟨[true, true], by simp⟩).1 = [false, true] := by
  rw [coe_varXor]
  decide

/-- Every ciphertext of a 2-bit word has two bits. -/
example (k : BitString 3) : (varXor 3 k ⟨[true, true], by simp⟩).1.length = 2 :=
  length_varXor 3 k _

/-- Decrypting `01` with the key `101` gives back `11`. -/
example : varXor 3 ![true, false, true] ⟨[false, true], by simp⟩ = ⟨[true, true], by simp⟩ := by
  have h : (⟨[false, true], by simp⟩ : {w : List Bool // w.length ≤ 3}) =
      varXor 3 ![true, false, true] ⟨[true, true], by simp⟩ :=
    Subtype.ext (by rw [coe_varXor]; decide)
  rw [h, varXor_varXor]

/-- With two key bits, a 1-bit message and a 2-bit message have different ciphertext laws. -/
example (b b' : Bool) :
    (variableLengthOTP 2).ciphertextDist ⟨[b], by simp⟩ ≠
      (variableLengthOTP 2).ciphertextDist ⟨[b, b'], by simp⟩ := by
  rw [Ne, variableLengthOTP_ciphertextDist_eq_iff]
  simp

/-- The book's first number: for every `L ≥ 1`, a 1-bit ciphertext has probability `1/2` under a
1-bit message. -/
example (L : ℕ) (hL : 1 ≤ L) (b c : Bool) :
    (variableLengthOTP L).ciphertextDist ⟨[b], by simpa using hL⟩ ⟨[c], by simpa using hL⟩ =
      1 / 2 := by
  rw [← map_apply_of_injective _ Subtype.val_injective, variableLengthOTP_ciphertextDist_map_val,
    List.length_singleton, BitString.uniformList_succ, BitString.uniformList_zero]
  simp only [PMF.pure_map]
  change ((uniformOfFintype Bool).bind (PMF.pure ∘ fun bit => [bit])) [c] = 1 / 2
  rw [PMF.bind_pure_comp, map_apply_of_injective _ (fun _ _ h => List.singleton_injective h),
    uniformOfFintype_apply, Fintype.card_bool, one_div, Nat.cast_ofNat]

/-- The book's second number: a 1-bit ciphertext has probability `0` under a 2-bit message. -/
example (b b' c : Bool) :
    (variableLengthOTP 2).ciphertextDist ⟨[b, b'], by simp⟩ ⟨[c], by simp⟩ = 0 :=
  variableLengthOTP_ciphertextDist_apply_of_length_ne (by simp)

/-- With one key bit the variable-length one-time pad is not perfectly secret. -/
example : ¬ (variableLengthOTP 1).PerfectlySecret :=
  not_perfectlySecret_variableLengthOTP one_pos

/-- With no key bits the only message is the empty word, and the cipher is perfectly secure. -/
example : (variableLengthOTP 0).CiphertextIndist :=
  (variableLengthOTP_ciphertextIndist_iff 0).mpr rfl

/-! ### The substitution cipher -/

/-- On words of two symbols over `Fin 2`, the message `00` never encrypts to `01`. -/
example : (substitutionCipher (Fin 2) 2).ciphertextDist (fun _ => 0) ![0, 1] = 0 := by
  rw [PMF.apply_eq_zero_iff]
  intro hc
  have := (substitutionCipher_apply_eq_iff hc 0 1).mpr rfl
  simp at this

/-- On words of two symbols over a three-letter alphabet, the substitution cipher is not perfectly
secure. -/
example : ¬ (substitutionCipher (Fin 3) 2).CiphertextIndist :=
  not_ciphertextIndist_substitutionCipher le_rfl

/-- The same cipher is not perfectly secret. -/
example : ¬ (substitutionCipher (Fin 3) 2).PerfectlySecret :=
  not_perfectlySecret_substitutionCipher le_rfl

/-- On words of one symbol over `Bool` the substitution cipher is perfectly secure, through the
counting criterion with `N_c = 1`: the hypothesis `2 ≤ L` cannot be dropped. -/
example : (substitutionCipher Bool 1).CiphertextIndist :=
  (EncScheme.ciphertextIndist_ofPure_uniformOfFintype_iff _ _ _).mpr fun c => ⟨1, fun m => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; revert m c; decide⟩

/-- Over a one-letter alphabet there is one message of each length, so the substitution cipher is
perfectly secure: the hypothesis `Nontrivial α` cannot be dropped. -/
example : (substitutionCipher Unit 2).CiphertextIndist := fun m₀ m₁ => by
  rw [Subsingleton.elim m₀ m₁]

end CslibFrontierTests.Crypto.PerfectSecrecyCiphers
