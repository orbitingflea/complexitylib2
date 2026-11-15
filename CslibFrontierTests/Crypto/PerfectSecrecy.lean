/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.PerfectSecrecy.Characterization
import Cslib.Crypto.Protocols.PerfectSecrecy.OneTimePad

/-!
# Characterizations of perfect security: checked instances

Checks for `CslibFrontier/Crypto/Protocols/PerfectSecrecy/Characterization.lean`, the
characterizations of perfect security in [BonehShoup2023] §2.1.2. The file is a `module` client
with ordinary imports.

* The counting criterion (Theorem 2.1, (i) ⇔ (ii)) accepts a cipher with two keys per message and
  ciphertext, and rejects the identity cipher with one key.
* The criterion `N_c = 1` proves the one-time pad `otp` perfectly secure, as the book proves
  Theorem 2.2.
* Theorem 2.3 in both directions: every event has the same probability under any two messages of
  the one-time pad, and the event `{true}` separates the two messages of the identity cipher.
* Full support is needed in the converse of Theorem 2.4: the identity cipher with a point-mass
  message law has independent message and ciphertext, and is not perfectly secure. With the
  uniform message law, the theorem shows that its message and ciphertext are dependent.
-/

namespace CslibFrontierTests.Crypto.PerfectSecrecy

open Cslib.Probability.PMF Cslib.Crypto.Protocols.PerfectSecrecy

/-! ### The counting criterion -/

/-- A cipher with `N_c = 2`: the key is two bits and only the first is used, so for each message
two keys give each ciphertext. -/
example : (EncScheme.ofPure (uniformOfFintype (Bool × Bool))
    (fun k (m : Bool) => xor k.1 m) (fun k c => xor k.1 c)
    (fun k m => by cases k.1 <;> cases m <;> rfl)).CiphertextIndist :=
  (EncScheme.ciphertextIndist_ofPure_uniformOfFintype_iff _ _ _).mpr fun c => ⟨2, fun m => by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]; revert m c; decide⟩

/-- The one-time pad `otp` through the criterion `N_c = 1`, with the key `c ⊕ m`: the
book's proof of Theorem 2.2. -/
example (l : ℕ) : (otp l).CiphertextIndist :=
  EncScheme.ciphertextIndist_ofPure_uniformOfFintype_of_existsUnique _ _ _ fun m c =>
    ⟨c ^^^ m, by simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero],
      fun k (hk : k ^^^ m = c) => by
        subst hk; simp only [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]⟩

/-- Theorem 2.3, forward: under the one-time pad every event on ciphertexts has the same
probability for any two messages. -/
example (l : ℕ) (S : Set (BitVec l)) (m₀ m₁ : BitVec l) :
    ((otp l).ciphertextDist m₀).toOuterMeasure S = ((otp l).ciphertextDist m₁).toOuterMeasure S :=
  (EncScheme.ciphertextIndist_iff_forall_toOuterMeasure _).mp
    ((EncScheme.perfectlySecret_iff_ciphertextIndist _).mp (otp_perfectlySecret l)) S m₀ m₁

/-! ### The identity cipher -/

/-- The identity cipher on one bit, with a single key. -/
public noncomputable def idCipher : EncScheme Bool Unit Bool :=
  .ofPure (uniformOfFintype Unit) (fun _ m => m) (fun _ c => c) fun _ _ => rfl

public theorem idCipher_ciphertextDist (m : Bool) : idCipher.ciphertextDist m = PMF.pure m :=
  (EncScheme.ciphertextDist_ofPure ..).trans (PMF.map_const _ m)

public theorem not_ciphertextIndist_idCipher : ¬ idCipher.CiphertextIndist := fun h => by
  simpa [idCipher_ciphertextDist] using DFunLike.congr_fun (h false true) false

/-- The counting criterion sees the same failure: `true` encrypts to `true` under one key and
`false` under none. -/
example : ¬ idCipher.CiphertextIndist := by
  rw [idCipher, EncScheme.ciphertextIndist_ofPure_uniformOfFintype_iff]
  rintro h
  obtain ⟨N, hN⟩ := h true
  have h₁ := hN true
  have h₂ := hN false
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) (by decide)

/-- Theorem 2.3, converse: the event `{true}` has probability `1` under the message `true` and `0`
under `false`, so the identity cipher is not perfectly secure. -/
example : ¬ idCipher.CiphertextIndist := fun h => by
  have := (EncScheme.ciphertextIndist_iff_forall_toOuterMeasure _).mp h {true} true false
  simp [idCipher_ciphertextDist] at this

/-! ### Full support in Theorem 2.4 -/

/-- Under the point-mass message law at `false`, message and ciphertext of the identity cipher
are independent, although the cipher is not perfectly secure (`not_ciphertextIndist_idCipher`):
`ciphertextIndist_iff_jointDist_eq_mul` needs a message law of full support. -/
example (m c : Bool) : idCipher.jointDist (PMF.pure false) (m, c) =
    PMF.pure false m * idCipher.marginalCiphertextDist (PMF.pure false) c := by
  have hmarg : idCipher.marginalCiphertextDist (PMF.pure false) = PMF.pure false :=
    (PMF.pure_bind false idCipher.ciphertextDist).trans (idCipher_ciphertextDist false)
  rw [EncScheme.jointDist_eq, hmarg, idCipher_ciphertextDist]
  cases m <;> cases c <;> simp

/-- Under the uniform message law on `Bool`, which has full support, message and ciphertext of the
identity cipher are dependent. -/
example : ¬ ∀ m c, idCipher.jointDist (uniformOfFintype Bool) (m, c) =
    uniformOfFintype Bool m * idCipher.marginalCiphertextDist (uniformOfFintype Bool) c :=
  mt (EncScheme.ciphertextIndist_iff_jointDist_eq_mul _ _ fun m => by simp).mpr
    not_ciphertextIndist_idCipher

end CslibFrontierTests.Crypto.PerfectSecrecy
