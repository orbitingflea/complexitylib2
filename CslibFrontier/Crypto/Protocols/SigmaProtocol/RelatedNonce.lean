/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.SchnorrSignature
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Schnorr signatures with related nonces

In Schnorr's random-oracle signature scheme ([BonehShoup2023], Section 19.2), signing two messages
`m₀ ≠ m₁` under nonces `r` and `a * r + b` with known `a, b : ZMod q` exposes the signing key via
`relatedNonceExtract` whenever `a * ι c₀ ≠ ι c₁` ([BonehShoup2023], Exercise 19.1). Under a lazily
sampled uniform random oracle, a two-query attacker recovers the secret key with probability at
least `1 - 1 / |C|` (`one_sub_inv_card_le_succProbability_relatedNonceGame`).

**Differences from Boneh–Shoup.** The book fixes a cyclic group with generator `g`, hashes to a
challenge set `C`, and states that the adversary recovers the secret key with high probability. Here
the ambient group is an additive `ZMod q`-module with an arbitrary base `g` and challenge embedding
`ι : C ↪ ZMod q` (`schnorrROMScheme`), for honest responses the formula returns the key for any base
`g` whenever `a * ι c₀ ≠ ι c₁` (`relatedNonceExtract_respond`), and the explicit lower bound
`1 - 1 / |C|` assumes `m₀ ≠ m₁` (needed because equal messages with `a = 1`, `b = 0` repeat the
random-oracle query and force `a * ι c₀ = ι c₁`). Only the exact-security typed ROM experiment is
defined here; polynomial-time word extraction is separate in
`CslibFrontier.Crypto.Computational.SchnorrRelatedNonce`, with no word-level game.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceExtract`: key-recovery formula, equal to
  `linearExtract` on the first conversation transformed by `schnorr_accepts_affine`.
* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceAttacker`: two-query ROM adversary outputting
  `relatedNonceExtract`.
* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceGame`: two-signature related-nonce experiment.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.schnorr_accepts_affine`: scaling and shifting an accepting
  Schnorr transcript scales its challenge by `a`.
* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceExtract_smul`: special soundness of
  `relatedNonceExtract`, deduced from `schnorr_specialSoundness`.
* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceExtract_respond`: honest-response key
  recovery without a group-generator hypothesis.
* `Cslib.Crypto.Protocols.SigmaProtocol.relatedNonceAttacker_isQueryBounded`: `relatedNonceAttacker`
  makes at most two hash queries.
* `Cslib.Crypto.Protocols.SigmaProtocol.one_sub_inv_card_le_succProbability_relatedNonceGame`:
  success probability at least `1 - 1 / |C|` for `m₀ ≠ m₁`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 19.2 and Exercise 19.1.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability OracleComp ROMSignature
open scoped ENNReal NNReal

section Algebra

variable {q : ℕ} [NeZero q] {G C : Type} [AddCommGroup G] [Module (ZMod q) G] [DecidableEq G]
  {ι : C ↪ ZMod q} {g : G}

/-- An accepting Schnorr conversation with nonce `r` gives, for the full challenge space, an
accepting conversation with nonce `a * r + b`: scale by `a` and shift by `b`. -/
theorem schnorr_accepts_affine {u t : G} {c : C} {z : ZMod q}
    (h : (schnorr ι g).Accepts u t c z) (a b : ZMod q) :
    (schnorr (Function.Embedding.refl (ZMod q)) g).Accepts u (a • t + b • g) (a * ι c)
      (a * z + b) := by
  rw [schnorr_accepts_iff] at h ⊢
  rw [Function.Embedding.refl_apply, add_smul, mul_smul, h, smul_add, mul_smul]
  abel

/-- The key computed from two Schnorr signatures whose nonces are `r` and `a * r + b`
([BonehShoup2023], Exercise 19.1): from the challenges `c₀, c₁` and the responses `z₀, z₁`. It is
`linearExtract` at the conversation transformed by `schnorr_accepts_affine`. -/
@[expose] def relatedNonceExtract (a b c₀ z₀ c₁ z₁ : ZMod q) : ZMod q :=
  (a * c₀ - c₁)⁻¹ * (a * z₀ + b - z₁)

/-- **Related nonces reveal a witness** ([BonehShoup2023], Exercise 19.1): from two accepting
conversations for `u` whose commitments satisfy `t₁ = a • t₀ + b • g`, with `a * ι c₀ ≠ ι c₁`. -/
theorem relatedNonceExtract_smul [Fact q.Prime] {u t₀ t₁ : G} {a b : ZMod q} {c₀ c₁ : C}
    {z₀ z₁ : ZMod q} (h₀ : (schnorr ι g).Accepts u t₀ c₀ z₀)
    (h₁ : (schnorr ι g).Accepts u t₁ c₁ z₁) (ht : t₁ = a • t₀ + b • g)
    (hc : a * ι c₀ ≠ ι c₁) :
    relatedNonceExtract a b (ι c₀) z₀ (ι c₁) z₁ • g = u := by
  have h₁' : (schnorr (Function.Embedding.refl (ZMod q)) g).Accepts u
      (a • t₀ + b • g) (ι c₁) z₁ := by
    rw [schnorr_accepts_iff] at h₁ ⊢
    rw [← ht]
    exact h₁
  exact schnorr_specialSoundness (ι := Function.Embedding.refl (ZMod q)) (g := g) u _ _ _ _ _ hc
    (schnorr_accepts_affine h₀ a b) h₁'

/-- **Related nonces reveal the signing key** ([BonehShoup2023], Exercise 19.1): from the honest
responses with nonces `r` and `a * r + b`, with `a * ι c₀ ≠ ι c₁`. No hypothesis on `g`. -/
theorem relatedNonceExtract_respond [Fact q.Prime] (α : ZMod q) (u : G) (r a b : ZMod q)
    {c₀ c₁ : C} (hc : a * ι c₀ ≠ ι c₁) :
    relatedNonceExtract a b (ι c₀) ((schnorr ι g).respond α u r c₀) (ι c₁)
      ((schnorr ι g).respond α u (a * r + b) c₁) = α := by
  have hne : a * ι c₀ - ι c₁ ≠ 0 := sub_ne_zero.mpr hc
  change (a * ι c₀ - ι c₁)⁻¹ * (a * (r + ι c₀ • α) + b - (a * r + b + ι c₁ • α)) = α
  rw [smul_eq_mul, smul_eq_mul, inv_mul_eq_iff_eq_mul₀ hne]
  ring

end Algebra

section RandomOracle

section Attacker

variable {q : ℕ} {G C M : Type}

/-- The adversary of [BonehShoup2023], Exercise 19.1 in the random-oracle model: recompute the two
challenges with two hash queries and return `relatedNonceExtract`. -/
@[expose] def relatedNonceAttacker (ι : C ↪ ZMod q) (a b : ZMod q) (m₀ : M) (σ₀ : G × ZMod q)
    (m₁ : M) (σ₁ : G × ZMod q) : OracleComp (fun _ : M × G => C) (ZMod q) := do
  let c₀ ← OracleComp.query (spec := fun _ : M × G => C) (m₀, σ₀.1)
  let c₁ ← OracleComp.query (spec := fun _ : M × G => C) (m₁, σ₁.1)
  return relatedNonceExtract a b (ι c₀) σ₀.2 (ι c₁) σ₁.2

/-- The adversary of [BonehShoup2023], Exercise 19.1 makes at most two hash queries. -/
theorem relatedNonceAttacker_isQueryBounded (ι : C ↪ ZMod q) (a b : ZMod q) (m₀ : M)
    (σ₀ : G × ZMod q) (m₁ : M) (σ₁ : G × ZMod q) :
    (relatedNonceAttacker ι a b m₀ σ₀ m₁ σ₁).IsQueryBounded 2 := by
  unfold relatedNonceAttacker
  exact (IsCostBounded.query _).bind fun _ => (IsCostBounded.query _).bind fun _ => .pure _ 0

end Attacker

variable {q : ℕ} [Fact q.Prime] {G C M : Type} [AddCommGroup G] [Module (ZMod q) G]
  [DecidableEq G] [DecidableEq M] [Fintype C] [Nonempty C]

/-- The experiment of [BonehShoup2023], Exercise 19.1: the Schnorr signer signs `m₀` with a uniform
nonce `r` and `m₁` with the nonce `a * r + b`, under one lazily sampled random oracle; the
adversary sees both signatures and wins when it returns the signing key. -/
@[expose] noncomputable def relatedNonceGame (ι : C ↪ ZMod q) (g : G) (a b : ZMod q)
    (m₀ m₁ : M) : Game := do
  let keys ← (schnorrROMScheme (M := M) ι g).keyGen
  let sk := keys.2
  let r ← PMF.uniformOfFintype (ZMod q)
  let s₀ ← (interpret (oracle C) ((schnorrROMScheme (M := M) ι g).sign sk m₀ (r • g, r))).run []
  let s₁ ← (interpret (oracle C)
    ((schnorrROMScheme (M := M) ι g).sign sk m₁ ((a * r + b) • g, a * r + b))).run s₀.2
  let x ← (interpret (oracle C) (relatedNonceAttacker ι a b m₀ s₀.1 m₁ s₁.1)).run s₁.2
  return decide (x.1 = sk.1)

/-- **Related-nonce key recovery** ([BonehShoup2023], Exercise 19.1): for two different messages
signed with affine-related nonces `r` and `a * r + b`, `relatedNonceAttacker` recovers the signing
key with probability at least `1 - 1 / |C|`. -/
theorem one_sub_inv_card_le_succProbability_relatedNonceGame (ι : C ↪ ZMod q) (g : G)
    (a b : ZMod q) {m₀ m₁ : M} (hm : m₀ ≠ m₁) :
    1 - (Fintype.card C : ℝ≥0)⁻¹ ≤ Game.succProbability (relatedNonceGame ι g a b m₀ m₁) := by
  have hfail : relatedNonceGame ι g a b m₀ m₁ false ≤ (Fintype.card C : ℝ≥0∞)⁻¹ := by
    simp only [relatedNonceGame, relatedNonceAttacker, schnorrROMScheme, fiatShamir, interpret_map,
      interpret_query, interpret_bind, interpret_pure, StateT.run_map, StateT.run_bind,
      StateT.run_pure, pmf_norm, PMF.monad_map_eq_map, PMF.bind_bind, PMF.pure_bind,
      PMF.map, Function.Embedding.refl_apply]
    refine PMF.bind_apply_le_on_support _ fun key _ => ?_
    refine PMF.bind_apply_le_on_support _ fun r _ => ?_
    rw [run_oracle_of_lookup_eq_none (cache := []) rfl]
    simp only [PMF.bind_bind, PMF.pure_bind]
    refine PMF.bind_apply_le_on_support _ fun c₀ _ => ?_
    have hne : ((m₁, (a * r + b) • g) == (m₀, r • g)) = false := by simp [Ne.symm hm]
    have hne' : ((m₀, r • g) == (m₁, (a * r + b) • g)) = false := by simp [hm]
    rw [run_oracle_of_lookup_eq_none (by simp [List.lookup, hne])]
    simp only [PMF.bind_bind, PMF.pure_bind]
    have hsum : ∑' c₁ : C, PMF.uniformOfFintype C c₁ *
        (if a * ι c₀ = ι c₁ then (1 : ℝ≥0∞) else 0) ≤ (Fintype.card C : ℝ≥0∞)⁻¹ := by
      simpa only [PMF.bind_apply, PMF.pure_apply, true_eq_decide_iff] using
        PMF.uniformOfFintype_bind_pure_apply_true_le (α := C)
          (E := fun c₁ => decide (a * ι c₀ = ι c₁)) fun x hx y hy =>
            ι.injective ((of_decide_eq_true hx).symm.trans (of_decide_eq_true hy))
    rw [PMF.bind_apply]
    refine le_trans (tsum_le_tsum fun c₁ => mul_le_mul_right ?_ _) hsum
    by_cases hc : a * ι c₀ = ι c₁
    · rw [ite_eq_left hc]
      exact PMF.coe_le_one _ _
    · rw [ite_eq_right hc, run_oracle_of_lookup_eq_some (c := c₀) (by simp [List.lookup, hne']),
        PMF.pure_bind, run_oracle_of_lookup_eq_some (c := c₁) (by simp [List.lookup]),
        PMF.pure_bind, relatedNonceExtract_respond key.1 key.2 r a b hc]
      simp
  have hf : Game.failProbability (relatedNonceGame ι g a b m₀ m₁) ≤
      (Fintype.card C : ℝ≥0)⁻¹ := by
    rw [Game.failProbability, ← ENNReal.toNNReal_coe ((Fintype.card C : ℝ≥0)⁻¹)]
    refine ENNReal.toNNReal_mono ENNReal.coe_ne_top ?_
    rwa [ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
  rw [tsub_le_iff_right]
  calc (1 : ℝ≥0) = Game.succProbability (relatedNonceGame ι g a b m₀ m₁) +
        Game.failProbability (relatedNonceGame ι g a b m₀ m₁) :=
        (Game.succProbability_add_failProbability _).symm
    _ ≤ _ := by gcongr

end RandomOracle

end Cslib.Crypto.Protocols.SigmaProtocol
