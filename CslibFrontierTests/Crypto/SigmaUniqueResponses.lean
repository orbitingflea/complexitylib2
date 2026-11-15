/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

import CslibFrontier.Crypto.Protocols.SigmaProtocol.UniqueResponses

/-!
# Tests for unique responses and strong special soundness

Hypothesis probes and concrete `ZMod 5` checks for
`CslibFrontier.Crypto.Protocols.SigmaProtocol.UniqueResponses`.
-/

namespace CslibFrontierTests.Crypto.SigmaUniqueResponses

open Cslib.Crypto.Protocols.SigmaProtocol

/-- Checks that Okamoto over `ZMod 5` with `g = h = 1` does not have unique responses at `0`:
`(1, 4)` and `(0, 0)` both answer commitment `0` on challenge `0`. -/
example : ¬ (okamoto (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5) 1).UniqueResponsesAt 0 := by
  intro h
  have := h 0 0 (1, 4) (0, 0) (by rw [okamoto_accepts_iff]; decide)
    (by rw [okamoto_accepts_iff]; decide)
  exact absurd this (by decide)

/-- Checks the `hg` injectivity hypothesis for Schnorr: over `ZMod 5` with `g = 0`, every
response is accepted so unique responses fail. -/
example : ¬ (schnorr (Function.Embedding.refl (ZMod 5)) (0 : ZMod 5)).UniqueResponses := by
  intro h
  have := h 0 0 0 0 1 (by rw [schnorr_accepts_iff]; decide) (by rw [schnorr_accepts_iff]; decide)
  exact absurd this (by decide)

/-- Checks that `UniqueResponses` is needed in `SpecialSoundness.strong`: for Okamoto over
`ZMod 5` with `g = h = 1`, statement `1`, the responses `(1, 0)` and `(0, 1)` to challenge `0` on
commitment `1` give `linearExtract = 0`, which is not a witness. -/
example : ¬ (okamoto (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5) 1).StrongSpecialSoundness
    (fun x u => x.1 • (1 : ZMod 5) + x.2 • (1 : ZMod 5) = u)
    (linearExtract (Function.Embedding.refl (ZMod 5))) := by
  intro h
  have := h 1 1 0 (1, 0) 0 (0, 1) (by decide) (by rw [okamoto_accepts_iff]; decide)
    (by rw [okamoto_accepts_iff]; decide)
  suffices h0 : (0 : ZMod 5) = 1 from absurd h0 (by decide)
  simpa [linearExtract] using this

/-- Checks the positive Schnorr instance over `ZMod 5` with `g = 1` for both `UniqueResponses`
and `schnorr_strongSpecialSoundness`, together with the Chaum–Pedersen specialization of
`SpecialSoundness.strong`. -/
example : (schnorr (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5)).UniqueResponses :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  schnorr_uniqueResponses (smul_left_injective (ZMod 5) one_ne_zero)

example : (schnorr (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5)).StrongSpecialSoundness
    (fun α u => α • (1 : ZMod 5) = u) (linearExtract (Function.Embedding.refl (ZMod 5))) :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  schnorr_strongSpecialSoundness one_ne_zero

example {q : ℕ} [NeZero q] [Fact q.Prime] {G C : Type} [AddCommGroup G] [Module (ZMod q) G]
    [DecidableEq G] {ι : C ↪ ZMod q} {g : G} (hg : g ≠ 0) :
    (chaumPedersen ι g).StrongSpecialSoundness (fun β (u, v, w) => β • g = v ∧ β • u = w)
      (linearExtract ι) :=
  chaumPedersen_specialSoundness.strong
    (chaumPedersen_uniqueResponses (smul_left_injective (ZMod q) hg))

/-- Checks that `[Nonempty C]` is needed in `linear_uniqueResponsesAt_iff`: with an empty
challenge type `Empty`, responses are vacuously unique even for the zero linear map on `ZMod 5`. -/
example : (linear (fun _ : Unit => (0 : ZMod 5 →ₗ[ZMod 5] ZMod 5)) (fun _ => 0)
    (Function.Embedding.ofIsEmpty : Empty ↪ ZMod 5)).UniqueResponsesAt () ∧
    ¬ Function.Injective (0 : ZMod 5 →ₗ[ZMod 5] ZMod 5) :=
  ⟨fun _ c => c.elim, fun h => absurd (h (a₁ := 0) (a₂ := 1) rfl) (by decide)⟩

/-- Checks `schnorr_uniqueResponsesAt_iff` negatively: `g = 0` over `ZMod 5` fails unique
responses at statement `3`. -/
example : ¬ (schnorr (Function.Embedding.refl (ZMod 5)) (0 : ZMod 5)).UniqueResponsesAt 3 :=
  fun h => absurd (schnorr_uniqueResponsesAt_iff.mp h (a₁ := 0) (a₂ := 1) (by simp)) (by decide)

/-- `3 α₀ = 2` over `ZMod 5`: the homogenized system has only `α₀ = 0`. -/
example : (linearSystem (Function.Embedding.refl (ZMod 5)) 1 1).UniqueResponsesAt
    ((fun _ _ => (3 : ZMod 5)), fun _ => 2) := by
  rw [linearSystem_uniqueResponsesAt_iff]
  intro α hα
  funext j
  have h0 := hα 0
  rw [Fin.sum_univ_one] at h0
  have hzero : ∀ x : ZMod 5, x • (3 : ZMod 5) = 0 → x = 0 := by decide
  rw [Subsingleton.elim j 0]
  exact hzero (α 0) h0

/-- `α₀ + α₁ = 2` over `ZMod 5`: the homogenized system has the solution `(1, 4)`. -/
example : ¬ (linearSystem (Function.Embedding.refl (ZMod 5)) 1 2).UniqueResponsesAt
    ((fun _ _ => (1 : ZMod 5)), fun _ => 2) := by
  rw [linearSystem_uniqueResponsesAt_iff]
  intro h
  exact absurd (congrFun (h ![1, 4] (by
    intro i
    simp only [smul_eq_mul, mul_one, Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    decide)) 0) (by decide)

/-- Checks `StrongSpecialSoundness.specialSoundness` on Schnorr over `ZMod 5`. -/
example : (schnorr (Function.Embedding.refl (ZMod 5)) (1 : ZMod 5)).SpecialSoundness
    (fun α u => α • (1 : ZMod 5) = u) (linearExtract (Function.Embedding.refl (ZMod 5))) :=
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  (schnorr_strongSpecialSoundness one_ne_zero).specialSoundness

end CslibFrontierTests.Crypto.SigmaUniqueResponses
