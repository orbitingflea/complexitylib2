/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.UniversalHash
public import CslibFrontier.Probability.Product
import CslibFrontier.Probability.StatisticalDistance.Product

/-!
# The leftover hash lemma for several independent samples

When the same public seed `k` of a universal or almost-universal hash family is used to hash
several mutually independent inputs `source : ι → PMF Input`, the resulting tuple of digests is
jointly close to independent uniform outputs even with `k` revealed. Conditioned on each seed `k`,
the coordinate digests `(source i).map (hash k)` are independent, so the hybrid bound for
conditionally independent products (`Cslib.Probability.PMF.dist_bind_pair_pi_le_sum`) sums the
single-sample leftover-hash bounds (`Cslib.Probability.IsUniversalHash.leftover_hash`) across
`i : ι`. Unlike `Cslib.Probability.IsTwoUniversal.leftover_hash_pi_conditional` in
`EntropyExtraction.lean`, which hashes a single joint tuple once, these theorems hash each
coordinate separately under one shared seed.

For a `(1 + α) / |Output|`-universal hash family and independent samples each of guessing
probability at most `γ`, the statistical distance to uniform is at most
`|ι| * √(|Output| * γ + α) / 2` ([BonehShoup2023], §8.10.4, Theorem 8.11, p. 334).

## Deviations from the book

* Samples are indexed by a finite type `ι` (`[Fintype ι] [DecidableEq ι]`) rather than
  `1, …, m`; their joint law is `PMF.pi source : PMF (ι → Input)` and the digest tuple lies in
  `ι → Output` (with `Fintype.card ι` in place of `m`).
* `Seed` and `Output` carry `[Fintype Seed]`, `[Fintype Output]` and `[Nonempty Output]`, and
  `Input` carries `[Finite Input]`.
* The guessing-probability bound $\max_{x \in \mathcal{S}} \Pr[s_i = x] \le \gamma$ is stated as
  the pointwise bound `∀ i x, (source i x).toReal ≤ γ` rather than a supremum over `Input`.
* The `(1 + α) / |Output|`-universal hypothesis in
  `IsUniversalHash.leftover_hash_pi_of_mass_le` and
  `IsUniversalHash.dist_seededHash_pi_uniformOfFintype_le` takes the explicit nonnegativity
  premise `hα : 0 ≤ 1 + α`. Mathematically a collision probability is nonnegative, so
  `0 ≤ (1 + α) / |Output|`; in Lean, `IsUniversalHash` takes an `ℝ≥0∞` bound and
  `ENNReal.ofReal ((1 + α) / Fintype.card Output)` clamps negative reals to `0`, which would
  otherwise make the premise hold for an injective hash on `Bool` at `α = -2` while the
  right-hand side evaluates to `0` against an actual distance of `1 / 2`.
* `IsUniversalHash.leftover_hash_pi` and `IsUniversalHash.leftover_hash_pi_of_mass_le` allow any
  seed distribution `seed : PMF Seed`, not only `PMF.uniformOfFintype Seed`;
  `IsUniversalHash.dist_seededHash_pi_uniformOfFintype_le` specializes to a uniform seed on
  `Seed` against `PMF.uniformOfFintype (Seed × (ι → Output))` as printed in Theorem 8.11.

## Main results

* `Cslib.Probability.IsUniversalHash.leftover_hash_pi`: multi-sample leftover hash lemma for
  `ε`-universal families in terms of each sample's collision probability.
* `Cslib.Probability.IsUniversalHash.leftover_hash_pi_of_mass_le`: Theorem 8.11 for an arbitrary
  seed distribution `seed : PMF Seed` under a pointwise guessing-probability bound `γ` and
  `0 ≤ 1 + α`.
* `Cslib.Probability.IsUniversalHash.dist_seededHash_pi_uniformOfFintype_le`: Theorem 8.11 as
  printed ([BonehShoup2023], §8.10.4, p. 334), comparing against
  `PMF.uniformOfFintype (Seed × (ι → Output))`.
* `Cslib.Probability.IsTwoUniversal.leftover_hash_pi`,
  `Cslib.Probability.IsTwoUniversal.leftover_hash_pi_of_mass_le`: specializations to two-universal
  hash families (`α = 0`).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.10.4,
  Theorem 8.11, p. 334.
-/

public section

namespace Cslib.Probability

open Cslib.Probability.PMF
open scoped BigOperators ENNReal

variable {Seed Input Output ι : Type*} [Fintype Seed] [Finite Input] [Fintype Output]
  [Fintype ι] [DecidableEq ι]

/-- Hybrid step for coordinatewise hashing under one shared seed, for any `hash`: the distance of
the digest tuple from a uniform tuple is at most the sum of the single-sample distances. -/
private theorem dist_seededHash_pi_le_sum [Nonempty Output] (seed : PMF Seed)
    (hash : Seed → Input → Output) (source : ι → PMF Input) :
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·))) ≤
      ∑ i, dist (seededHash seed (source i) hash)
        (seed.bind (fun s => (PMF.uniformOfFintype Output).map (s, ·))) := by
  have hsum := dist_bind_pair_pi_le_sum seed
    (fun s i => (source i).map (hash s))
    (fun _ _ => PMF.uniformOfFintype Output)
  simp only [PMF.pi_map source (fun _ => hash _), PMF.pi_uniformOfFintype] at hsum
  simpa only [seededHash, PMF.map_comp, Function.comp_def] using hsum

/-- **Multi-sample leftover hash lemma** for `ε`-universal families: hashing independent samples
under one shared public seed is within the sum of the single-sample leftover-hash bounds of the
seed paired with an independent uniform tuple. -/
theorem IsUniversalHash.leftover_hash_pi [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} {ε : ℝ≥0∞} (hhash : IsUniversalHash seed hash ε)
    (hε : ε ≠ ⊤) (source : ι → PMF Input) :
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·))) ≤
      ∑ i, Real.sqrt
        (Fintype.card Output * (collisionProbability (source i) + ε.toReal) - 1) / 2 :=
  (dist_seededHash_pi_le_sum seed hash source).trans
    (Finset.sum_le_sum fun i _ => hhash.leftover_hash hε (source i))

/-- **Theorem 8.11 (Leftover Hash Lemma for several samples)** ([BonehShoup2023], §8.10.4,
p. 334), for any seed distribution: if `hash` is `(1 + α) / |Output|`-universal with `0 ≤ 1 + α`
and each independent sample `source i` has guessing probability at most `γ`, then hashing all
samples under one shared public seed is within `|ι| * √(|Output| * γ + α) / 2` of the seed paired
with an independent uniform tuple. -/
theorem IsUniversalHash.leftover_hash_pi_of_mass_le [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} {α γ : ℝ} (hα : 0 ≤ 1 + α)
    (hhash : IsUniversalHash seed hash (ENNReal.ofReal ((1 + α) / Fintype.card Output)))
    (source : ι → PMF Input) (hmass : ∀ i x, (source i x).toReal ≤ γ) :
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·))) ≤
      Fintype.card ι * Real.sqrt (Fintype.card Output * γ + α) / 2 := by
  have hcard : (Fintype.card Output : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hε_nonneg : 0 ≤ (1 + α) / Fintype.card Output := div_nonneg hα (Nat.cast_nonneg _)
  calc
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·)))
      ≤ ∑ i, Real.sqrt (Fintype.card Output *
          (collisionProbability (source i) +
            (ENNReal.ofReal ((1 + α) / Fintype.card Output)).toReal) - 1) / 2 :=
        hhash.leftover_hash_pi ENNReal.ofReal_ne_top source
    _ ≤ ∑ _i : ι, Real.sqrt (Fintype.card Output * γ + α) / 2 := by
        refine Finset.sum_le_sum fun i _ => div_le_div_of_nonneg_right (Real.sqrt_le_sqrt ?_)
          (by norm_num)
        rw [ENNReal.toReal_ofReal hε_nonneg, mul_add, mul_div_cancel₀ _ hcard]
        have hcp : collisionProbability (source i) ≤ γ :=
          collisionProbability_le_of_mass_le (source i) (hmass i)
        have hmul : (Fintype.card Output : ℝ) * collisionProbability (source i) ≤
            Fintype.card Output * γ :=
          mul_le_mul_of_nonneg_left hcp (Nat.cast_nonneg _)
        linarith
    _ = Fintype.card ι * Real.sqrt (Fintype.card Output * γ + α) / 2 := by
        simp [mul_div_assoc]

/-- **Theorem 8.11 (Leftover Hash Lemma)** as printed ([BonehShoup2023], §8.10.4, p. 334):
for a `(1 + α) / |Output|`-universal hash function with `0 ≤ 1 + α`, a uniform seed on `Seed`, and
independent samples `source i` each with guessing probability at most `γ`, the statistical distance
between `(k, fun i => hash k (s i))` and the uniform distribution on `Seed × (ι → Output)` is at
most `|ι| * √(|Output| * γ + α) / 2`. -/
theorem IsUniversalHash.dist_seededHash_pi_uniformOfFintype_le [Nonempty Seed] [Nonempty Output]
    {hash : Seed → Input → Output} {α γ : ℝ} (hα : 0 ≤ 1 + α)
    (hhash : IsUniversalHash (PMF.uniformOfFintype Seed) hash
      (ENNReal.ofReal ((1 + α) / Fintype.card Output)))
    (source : ι → PMF Input) (hmass : ∀ i x, (source i x).toReal ≤ γ) :
    dist (seededHash (PMF.uniformOfFintype Seed) (PMF.pi source) (fun s x i => hash s (x i)))
        (PMF.uniformOfFintype (Seed × (ι → Output))) ≤
      Fintype.card ι * Real.sqrt (Fintype.card Output * γ + α) / 2 := by
  rw [← PMF.uniformOfFintype_prod]
  exact hhash.leftover_hash_pi_of_mass_le hα source hmass

/-- **Multi-sample leftover hash lemma** for universal families (`α = 0`): hashing independent
samples under one shared public seed is within
`∑ i, √(|Output| * collisionProbability (source i)) / 2` of the seed paired with an independent
uniform tuple. -/
theorem IsTwoUniversal.leftover_hash_pi [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (source : ι → PMF Input) :
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·))) ≤
      ∑ i, Real.sqrt (Fintype.card Output * collisionProbability (source i)) / 2 :=
  (dist_seededHash_pi_le_sum seed hash source).trans
    (Finset.sum_le_sum fun i _ => hhash.leftover_hash (source i))

/-- **Multi-sample leftover hash lemma** for universal families (`α = 0`) under a pointwise
guessing-probability bound `γ` on each sample. -/
theorem IsTwoUniversal.leftover_hash_pi_of_mass_le [Nonempty Output] {seed : PMF Seed}
    {hash : Seed → Input → Output} (hhash : IsTwoUniversal seed hash)
    (source : ι → PMF Input) {γ : ℝ} (hmass : ∀ i x, (source i x).toReal ≤ γ) :
    dist (seededHash seed (PMF.pi source) (fun s x i => hash s (x i)))
        (seed.bind (fun s => (PMF.uniformOfFintype (ι → Output)).map (s, ·))) ≤
      Fintype.card ι * Real.sqrt (Fintype.card Output * γ) / 2 := by
  refine (dist_seededHash_pi_le_sum seed hash source).trans
    ((Finset.sum_le_sum fun i _ => hhash.leftover_hash_of_mass_le (source i) (hmass i)).trans_eq ?_)
  simp [mul_div_assoc]

end Cslib.Probability
