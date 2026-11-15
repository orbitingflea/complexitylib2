/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import Cslib.Probability.StatisticalDistance
import CslibFrontier.Probability.StatisticalDistance.TotalVariation

/-!
# Statistical indistinguishability of ensembles

`StatisticallyIndistinguishable X Y` formalizes [BonehShoup2023], Definition 3.6 (p. 85), in the
asymptotic reading of Section 3.11.1 (p. 87): two ensembles `X Y : ∀ n, PMF (α n)` have
statistical distance bounded by a single negligible function `ε : ℕ → ℝ≥0` at every `n`.

This development differs from the book's presentation as follows:

1. **Asymptotic ensembles on arbitrary types.** The types `α n` are arbitrary `Type`s, not
   required to be finite or bit strings of polynomial length. Distance is measured by
   `Cslib.Probability.CloseTo` so it applies without `Fintype`, and agrees with
   `Negligible fun n => nndist (X n) (Y n)` on finite types
   (`statisticallyIndistinguishable_iff_negligible_nndist`).
2. **Characterization by unbounded tests.** `statisticallyIndistinguishable_iff_indistinguishable`
   equates statistical indistinguishability with `Game.Indistinguishable` with admissibility
   `fun _ => True`, proved via `Game.closeTo_advantage_map_decide_lt` without finiteness.
3. **Scope.** Theorem 3.10 in `max = Δ` form, Remark 3.1, and Exercises 3.10–3.14 are omitted.
   Game-specific statistical notions such as `CommitmentScheme.StatisticalHiding` are not instances
   and are not changed.

## Main definitions

* `Cslib.Crypto.StatisticallyIndistinguishable`: negligible `CloseTo` distance between two
  ensembles on arbitrary types.

## Main results

* `Cslib.Crypto.StatisticallyIndistinguishable.refl`,
  `Cslib.Crypto.StatisticallyIndistinguishable.symm`,
  `Cslib.Crypto.StatisticallyIndistinguishable.trans`: equivalence relation on ensembles.
* `Cslib.Crypto.StatisticallyIndistinguishable.map`: closure under arbitrary deterministic
  postprocessing ([BonehShoup2023], Theorem 3.13, p. 85, extended beyond finite types).
* `Cslib.Crypto.StatisticallyIndistinguishable.bind`: Markov-kernel postprocessing under
  arbitrary randomized maps, via `CloseTo.bind_left`.
* `Cslib.Crypto.StatisticallyIndistinguishable.indistinguishable`: negligible advantage against
  every family of randomized tests ([BonehShoup2023], Theorem 3.11, p. 84).
* `Cslib.Crypto.StatisticallyIndistinguishable.of_dist_le`: finite-type entry point from a
  negligible bound on `dist`.
* `Cslib.Crypto.statisticallyIndistinguishable_iff_indistinguishable`: equivalence with
  `Game.Indistinguishable` against all randomized tests.
* `Cslib.Crypto.statisticallyIndistinguishable_iff_negligible_nndist`: equivalence with
  negligible `nndist` on finite types.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 3.11 (Theorem 3.10, p. 83; Theorem 3.11, p. 84; Definition 3.6 and Theorem 3.13,
  p. 85) and Section 3.11.1 (p. 87).
-/

public section

namespace Cslib.Crypto

open Cslib Cslib.Probability
open scoped NNReal ENNReal Cslib.Probability.PMF

/-- **Statistical indistinguishability** ([BonehShoup2023], Definition 3.6, p. 85, read
asymptotically as in Section 3.11.1, p. 87): the statistical distance between `X n` and `Y n` is
bounded by a negligible function of the security parameter `n`. -/
@[expose] def StatisticallyIndistinguishable {α : ℕ → Type} (X Y : ∀ n, PMF (α n)) : Prop :=
  ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, CloseTo (X n) (Y n) (ε n)

namespace StatisticallyIndistinguishable

variable {α β : ℕ → Type} {X Y Z : ∀ n, PMF (α n)}

/-- An ensemble is statistically indistinguishable from itself. -/
theorem refl (X : ∀ n, PMF (α n)) : StatisticallyIndistinguishable X X :=
  ⟨fun _ => 0, negligible_zero, fun n => by simp⟩

/-- Statistical indistinguishability is symmetric. -/
theorem symm (h : StatisticallyIndistinguishable X Y) : StatisticallyIndistinguishable Y X := by
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun n => (h n).symm⟩

/-- Statistical indistinguishability is transitive: the two negligible bounds add. -/
theorem trans (hXY : StatisticallyIndistinguishable X Y)
    (hYZ : StatisticallyIndistinguishable Y Z) : StatisticallyIndistinguishable X Z := by
  obtain ⟨ε, hε, h₁⟩ := hXY
  obtain ⟨δ, hδ, h₂⟩ := hYZ
  exact ⟨ε + δ, hε.add hδ, fun n => by simpa using (h₁ n).trans (h₂ n)⟩

/-- Applying a function to both ensembles preserves statistical indistinguishability
([BonehShoup2023], Theorem 3.13, p. 85, for ensembles). The function need not be efficient. -/
theorem map (h : StatisticallyIndistinguishable X Y) (f : ∀ n, α n → β n) :
    StatisticallyIndistinguishable (fun n => (X n).map (f n)) (fun n => (Y n).map (f n)) := by
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun n => (h n).map (f n)⟩

/-- Randomized postprocessing of both ensembles preserves statistical indistinguishability. -/
theorem bind (h : StatisticallyIndistinguishable X Y) (f : ∀ n, α n → PMF (β n)) :
    StatisticallyIndistinguishable (fun n => (X n).bind (f n)) (fun n => (Y n).bind (f n)) := by
  obtain ⟨ε, hε, h⟩ := h
  exact ⟨ε, hε, fun n => (h n).bind_left (f n)⟩

/-- Every family of randomized tests, efficient or not, has negligible advantage between
statistically indistinguishable ensembles ([BonehShoup2023], Theorem 3.11, p. 84, in the
asymptotic reading of Section 3.11.1, p. 87). -/
theorem indistinguishable (h : StatisticallyIndistinguishable X Y) :
    Game.Indistinguishable (fun (test : ∀ n, α n → Game) n => (X n).bind (test n))
      (fun test n => (Y n).bind (test n)) (fun _ => True) := by
  obtain ⟨ε, hε, h⟩ := h
  exact fun test _ => negligible_of_le hε fun n => Game.advantage_bind_le_of_closeTo (h n) (test n)

/-- On finite types, a negligible bound on the statistical distance `dist (X n) (Y n)` gives
statistical indistinguishability. With upstream `PMF.StatisticallyClose (X n) (Y n) (ε n)`, which
unfolds to this bound, this is the entry point from the finite metric. -/
theorem of_dist_le [∀ n, Fintype (α n)] {ε : ℕ → ℝ≥0} (hε : Negligible ε)
    (h : ∀ n, dist (X n) (Y n) ≤ ε n) : StatisticallyIndistinguishable X Y :=
  ⟨ε, hε, fun n => closeTo_of_dist_le (h n)⟩

end StatisticallyIndistinguishable

/-- Statistical indistinguishability is indistinguishability by every family of randomized tests,
with no efficiency condition: the distance is negligible exactly when every test family has
negligible advantage. -/
theorem statisticallyIndistinguishable_iff_indistinguishable {α : ℕ → Type}
    {X Y : ∀ n, PMF (α n)} :
    StatisticallyIndistinguishable X Y ↔
      Game.Indistinguishable (fun (test : ∀ n, α n → Game) n => (X n).bind (test n))
        (fun test n => (Y n).bind (test n)) (fun _ => True) := by
  refine ⟨fun h => h.indistinguishable, fun h => ?_⟩
  refine ⟨_, h (fun n a => PMF.pure (decide (Y n a < X n a))) trivial, fun n => ?_⟩
  exact Game.closeTo_advantage_map_decide_lt (X n) (Y n)

/-- On finite types, statistical indistinguishability says that the statistical distance
`dist (X n) (Y n)` of [BonehShoup2023], Definition 3.5, is negligible: Definition 3.6 as printed. -/
theorem statisticallyIndistinguishable_iff_negligible_nndist {α : ℕ → Type}
    [∀ n, Fintype (α n)] {X Y : ∀ n, PMF (α n)} :
    StatisticallyIndistinguishable X Y ↔ Negligible fun n => nndist (X n) (Y n) := by
  constructor
  · rintro ⟨ε, hε, h⟩
    exact negligible_of_le hε fun n => by
      have hd := closeTo_coe_iff_dist_le.mp (h n)
      rw [← NNReal.coe_le_coe, coe_nndist]
      exact hd
  · intro h
    exact ⟨_, h, fun n => closeTo_coe_iff_dist_le.mpr (by rw [coe_nndist])⟩

end Cslib.Crypto
