/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.PMF
import Mathlib.Data.List.GetD

/-!
# Choosing a list entry by a uniform index

An index drawn uniformly below `Q` and read as a position in a list selects each of the list's
first `Q` entries with probability at least `1 / Q`. Positions at or beyond the end of the list
select the default value. This is the guessing step of a reduction that cannot recognize the right
answer among an adversary's candidates and outputs one of them at random, as in
[BonehShoup2023], Section 11.5.1, proof of Theorem 11.4 (pp. 446–448), and Section 21.11.4
(p. 908).

The bound holds for every list. Entries beyond the first `Q` are never selected by an index below
`Q`, so membership in `l.take Q`, not in `l`, is what the bound needs; for a list of length at most
`Q` the two agree. Repeated entries only add to the probability.

## Main results

* `Cslib.Probability.PMF.inv_le_map_uniformOfFintype_getD`: a member of `l.take Q` is selected
  with probability at least `1 / Q`.
* `Cslib.Probability.PMF.inv_le_map_uniformOfFintype_getD_of_length_le`: the same for a member of
  a list of length at most `Q`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 11.5.1, proof of Theorem 11.4, pp. 446–448, and
  Section 21.11.4, p. 908.
-/

public section

namespace Cslib.Probability.PMF

open scoped ENNReal

variable {α : Type*}

/-- **Guessing a list entry**: an index drawn uniformly below `Q`, read as a position in `l` with
default `d`, selects a member `x` of the first `Q` entries of `l` with probability at least
`1 / Q`. There is no hypothesis on the length of `l`, and the default is arbitrary. -/
theorem inv_le_map_uniformOfFintype_getD {Q : ℕ} [NeZero Q] {l : List α} {x : α} (d : α)
    (hx : x ∈ l.take Q) :
    (Q : ℝ≥0∞)⁻¹ ≤ (PMF.uniformOfFintype (Fin Q)).map (fun i : Fin Q => l.getD i d) x := by
  classical
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take] at hi
  have hiQ : i < Q := lt_of_lt_of_le hi (min_le_left _ _)
  have hil : i < l.length := lt_of_lt_of_le hi (min_le_right _ _)
  have hsel : (l.take Q)[i] = l.getD (⟨i, hiQ⟩ : Fin Q) d := by
    simp [List.getElem_take, List.getElem?_eq_getElem hil]
  rw [PMF.map_apply]
  refine le_trans (le_of_eq ?_) (le_tsum _ (⟨i, hiQ⟩ : Fin Q))
  simp [hsel, PMF.uniformOfFintype_apply]

/-- **Guessing an entry of a short list**: an index drawn uniformly below `Q`, read as a position
in a list `l` of length at most `Q` with default `d`, selects a member `x` of `l` with probability
at least `1 / Q`. -/
theorem inv_le_map_uniformOfFintype_getD_of_length_le {Q : ℕ} [NeZero Q] {l : List α} {x : α}
    (d : α) (hl : l.length ≤ Q) (hx : x ∈ l) :
    (Q : ℝ≥0∞)⁻¹ ≤ (PMF.uniformOfFintype (Fin Q)).map (fun i : Fin Q => l.getD i d) x :=
  inv_le_map_uniformOfFintype_getD d (by rwa [List.take_of_length_le hl])

end Cslib.Probability.PMF
