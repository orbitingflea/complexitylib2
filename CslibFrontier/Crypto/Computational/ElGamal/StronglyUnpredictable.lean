/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Crypto.Computational.Encryption.StronglyUnpredictable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Probability.PMF.Map

/-!
# Strong ciphertext unpredictability of ElGamal encryption

Over a `PrimeOrderGroupFamily`, both multiplicative ElGamal encryption (`elGamalEncryptProb`) and
hybrid Hashed ElGamal encryption (`Encryption.hybridEncrypt (F.hashedElGamalEncapsProb H d)
encryptSym`) have strongly unpredictable ciphertexts ([BonehShoup2023], §21.4.1, p. 872) whenever
the reciprocal group order `(F.order (d n) : ℝ≥0)⁻¹` is negligible along the parameter schedule `d`.

Neither `elGamalEncryptProb` nor `hashedElGamalEncapsProb` checks whether `pk` is a well-formed
group element: the ciphertext prefix `β • g` depends only on the fresh ephemeral exponent `b`, and
the modular sampling error `1 / 2 ^ n` from `sampleExp` gives the explicit single-invocation hit
bound `(F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n`. Whenever the deterministic group schedule
`fun n => PMF.pure (d n)` satisfies `F.DDH`, `DDH.negligible_expected_inv_order` implies that
`(F.order (d n) : ℝ≥0)⁻¹` is negligible.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.eval_bind_sampleExp_apply_le`: shared ciphertext-hit bound
  for any `sampleExp`-based computation whose output uniquely determines `b mod q`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ciphertextHitBound_elGamalEncryptProb`: single-parameter hit
  bound `(F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n` for multiplicative ElGamal.
* `Cslib.Crypto.PrimeOrderGroupFamily.stronglyUnpredictable_elGamalEncryptProb`: strong
  unpredictability of multiplicative ElGamal under negligible reciprocal group order.
* `Cslib.Crypto.PrimeOrderGroupFamily.ciphertextHitBound_hybrid_hashedElGamal`: single-parameter
  hit bound for hybrid Hashed ElGamal with any DEM `encryptSym`.
* `Cslib.Crypto.PrimeOrderGroupFamily.stronglyUnpredictable_hybrid_hashedElGamal`: strong
  unpredictability of hybrid Hashed ElGamal under negligible reciprocal group order.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section
  21.4.1 (p. 872), Section 11.5 (pp. 445–446), Exercise 11.5 (p. 459), and Exercise 11.9
  (pp. 460–461).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Cslib.Crypto.Encryption Cslib.Probability Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- Shared hit-bound lemma for any computation that binds `b ← F.sampleExp n d` and whose
output `x` uniquely determines `(b : ZMod (F.order d))`. -/
theorem eval_bind_sampleExp_apply_le (F : PrimeOrderGroupFamily)
    {α : Type} (n : ℕ) (d : F.Desc)
    (body : ℕ → ProbComp α)
    (x : α)
    (hdet : ∀ b₁ b₂ : ℕ,
      ProbComp.eval (body b₁) x ≠ 0 →
      ProbComp.eval (body b₂) x ≠ 0 →
      (b₁ : ZMod (F.order d)) = (b₂ : ZMod (F.order d))) :
    ((ProbComp.eval (do let b ← F.sampleExp n d; body b)) x).toNNReal ≤
      (F.order d : ℝ≥0)⁻¹ + 1 / 2 ^ n := by
  by_cases hex : ∃ b₀ : ℕ, ProbComp.eval (body b₀) x ≠ 0
  · rcases hex with ⟨b₀, hb₀⟩
    let β₀ : ZMod (F.order d) := (b₀ : ZMod (F.order d))
    let gReal : Game := (ProbComp.eval (F.sampleExp n d)).bind fun b =>
      PMF.pure (decide ((b : ZMod (F.order d)) = β₀))
    let gIdeal : Game := (PMF.uniformOfFintype (ZMod (F.order d))).bind
      fun β => PMF.pure (decide (β = β₀))
    have hle_ind :
        (ProbComp.eval (do let b ← F.sampleExp n d; body b)) x ≤ gReal true := by
      rw [ProbComp.eval_bind, PMF.bind_apply]
      dsimp only [gReal]
      rw [PMF.bind_apply]
      refine tsum_le_tsum fun b => ?_
      by_cases hb : ProbComp.eval (body b) x = 0
      · simp [hb]
      · have hβ : (b : ZMod (F.order d)) = β₀ := hdet b b₀ hb hb₀
        simp only [hβ, PMF.pure_apply, decide_true, ↓reduceIte, mul_one]
        exact mul_le_of_le_one_right' (PMF.coe_le_one _ _)
    have hadv : Game.advantage gReal gIdeal ≤ 1 / 2 ^ n :=
      F.advantage_bind_sampleExp_le n d (fun β => PMF.pure (decide (β = β₀)))
    have hideal : gIdeal.succProbability = (F.order d : ℝ≥0)⁻¹ := by
      apply NNReal.eq
      rw [Game.succProbability]
      have hval : gIdeal true = (F.order d : ℝ≥0∞)⁻¹ := by
        dsimp only [gIdeal]
        rw [PMF.bind_apply, tsum_fintype]
        simp [PMF.uniformOfFintype_apply, PMF.pure_apply, ZMod.card]
      rw [hval]
      simp
    have hreal_le : gReal.succProbability ≤ (F.order d : ℝ≥0)⁻¹ + 1 / 2 ^ n := by
      rw [← NNReal.coe_le_coe, NNReal.coe_add, ← hideal]
      have hadv' : |(gReal.succProbability : ℝ) - gIdeal.succProbability| ≤
          ((1 / 2 ^ n : ℝ≥0) : ℝ) := by
        rw [← Game.coe_advantage]
        exact NNReal.coe_le_coe.mpr hadv
      linarith [le_abs_self ((gReal.succProbability : ℝ) - gIdeal.succProbability)]
    exact (ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) hle_ind).trans hreal_le
  · push Not at hex
    have hzero : (ProbComp.eval (do let b ← F.sampleExp n d; body b)) x = 0 := by
      rw [ProbComp.eval_bind, PMF.bind_apply]
      simp [hex]
    rw [hzero]
    simp

/-- At each security parameter `n`, multiplicative ElGamal encryption `elGamalEncryptProb` has
ciphertext hit bound `(F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n`, uniformly over all public keys and
messages. -/
theorem ciphertextHitBound_elGamalEncryptProb (F : PrimeOrderGroupFamily)
    {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc) (n : ℕ) :
    CiphertextHitBound
      (fun pk m => some <$> F.elGamalEncryptProb encodeMsg d n pk m)
      ((F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n) := by
  refine (ciphertextHitBound_map_some_iff _ _).mpr fun pk m c => ?_
  unfold elGamalEncryptProb
  refine F.eval_bind_sampleExp_apply_le n (d n)
    (fun b => pure (encPair encBits encBits
      (F.encodeElGamalEncrypt (d n, dropFrame pk, encodeMsg (d n) m, b)))) c ?_
  intro b₁ b₂ h₁ h₂
  simp only [ProbComp.eval_pure, PMF.pure_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
    not_not] at h₁ h₂
  have hu₁ := (congrArg unframe h₁).trans (unframe_encPair_encBits _ _ _)
  have hu₂ := (congrArg unframe h₂).trans (unframe_encPair_encBits _ _ _)
  have hsmul : F.smul (d n, b₁, F.encode (d n) (F.generator (d n))) =
      F.smul (d n, b₂, F.encode (d n) (F.generator (d n))) := by
    simpa [encodeElGamalEncrypt] using hu₁.symm.trans hu₂
  simp only [F.smul_encode] at hsmul
  exact F.smul_generator_injective (d n) (F.encode_injective (d n) hsmul)

/-- Multiplicative ElGamal encryption `elGamalEncryptProb` has strongly unpredictable ciphertexts
([BonehShoup2023], §21.4.1, p. 872) whenever `(F.order (d n) : ℝ≥0)⁻¹` is negligible. In
particular, `hord` follows from `F.DDH (fun n => PMF.pure (d n))` via
`DDH.negligible_expected_inv_order`. -/
theorem stronglyUnpredictable_elGamalEncryptProb (F : PrimeOrderGroupFamily)
    {Msg : Type} (encodeMsg : F.Desc → Msg → List Bool)
    (d : ℕ → F.Desc)
    (hord : Negligible fun n => (F.order (d n) : ℝ≥0)⁻¹) :
    StronglyUnpredictable
      (fun n pk m => some <$> F.elGamalEncryptProb encodeMsg d n pk m) :=
  StronglyUnpredictable.of_bound (hord.add negligible_one_div_two_pow)
    (F.ciphertextHitBound_elGamalEncryptProb encodeMsg d)

/-- At each security parameter `n`, hybrid Hashed ElGamal encryption
`Encryption.hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym` has ciphertext hit bound
`(F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n`, uniformly over all public keys, messages, and symmetric
encryption components `encryptSym`. -/
theorem ciphertextHitBound_hybrid_hashedElGamal (F : PrimeOrderGroupFamily)
    {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (d : ℕ → F.Desc) (n : ℕ) :
    CiphertextHitBound
      (fun pk m =>
        some <$> Encryption.hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym n pk m)
      ((F.order (d n) : ℝ≥0)⁻¹ + 1 / 2 ^ n) := by
  refine (ciphertextHitBound_map_some_iff _ _).mpr fun pk m c => ?_
  unfold Encryption.hybridEncrypt hashedElGamalEncapsProb
  rw [bind_assoc]
  refine F.eval_bind_sampleExp_apply_le n (d n)
    (fun b => do
      let ctDem ← encryptSym n (H (d n, F.smul (d n, b, dropFrame pk))) m
      return encPair encBits encBits
        (F.smul (d n, b, F.encode (d n) (F.generator (d n))), ctDem)) c ?_
  intro b₁ b₂ h₁ h₂
  have extract (b : ℕ)
      (hb : ProbComp.eval (do
        let ctDem ← encryptSym n (H (d n, F.smul (d n, b, dropFrame pk))) m
        return encPair encBits encBits
          (F.smul (d n, b, F.encode (d n) (F.generator (d n))), ctDem)) c ≠ 0) :
      unframe c = F.encode (d n) ((b : ZMod (F.order (d n))) • F.generator (d n)) := by
    rw [ProbComp.eval_bind, PMF.bind_apply] at hb
    have hex : ∃ ctDem,
        ProbComp.eval (encryptSym n (H (d n, F.smul (d n, b, dropFrame pk))) m) ctDem *
          ProbComp.eval (pure (encPair encBits encBits
            (F.smul (d n, b, F.encode (d n) (F.generator (d n))), ctDem))) c ≠ 0 := by
      by_contra hnone
      push Not at hnone
      exact hb (tsum_eq_zero_iff.mpr hnone)
    rcases hex with ⟨ctDem, hterm⟩
    have hp : ProbComp.eval (pure (encPair encBits encBits
        (F.smul (d n, b, F.encode (d n) (F.generator (d n))), ctDem))) c ≠ 0 :=
      right_ne_zero_of_mul hterm
    simp only [ProbComp.eval_pure, PMF.pure_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
      not_not] at hp
    have hu := (congrArg unframe hp).trans (unframe_encPair_encBits _ _ _)
    simpa [F.smul_encode] using hu
  exact F.smul_generator_injective (d n)
    (F.encode_injective (d n) ((extract b₁ h₁).symm.trans (extract b₂ h₂)))

/-- Hybrid Hashed ElGamal encryption has strongly unpredictable ciphertexts ([BonehShoup2023],
§21.4.1, p. 872) whenever `(F.order (d n) : ℝ≥0)⁻¹` is negligible. In particular, `hord` follows
from `F.DDH (fun n => PMF.pure (d n))` via `DDH.negligible_expected_inv_order`. -/
theorem stronglyUnpredictable_hybrid_hashedElGamal (F : PrimeOrderGroupFamily)
    {Msg : Type} (H : F.Desc × List Bool → List Bool)
    (encryptSym : ℕ → List Bool → Msg → ProbComp (List Bool))
    (d : ℕ → F.Desc)
    (hord : Negligible fun n => (F.order (d n) : ℝ≥0)⁻¹) :
    StronglyUnpredictable
      (fun n pk m =>
        some <$> Encryption.hybridEncrypt (F.hashedElGamalEncapsProb H d) encryptSym n pk m) :=
  StronglyUnpredictable.of_bound (hord.add negligible_one_div_two_pow)
    (F.ciphertextHitBound_hybrid_hashedElGamal H encryptSym d)

end Cslib.Crypto.PrimeOrderGroupFamily
