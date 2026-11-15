/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Languages.Probabilistic.UniformNat.LowerBound
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Probability.PMF.UniformIndex
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# The list form of the Computational Diffie–Hellman problem in a fixed group

A list adversary receives `a • g` and `b • g` and returns a list of group elements; it wins when
the Diffie–Hellman value `(a * b) • g` is among the first `Q` entries of its list. A CDH adversary
that runs it and returns the entry at a uniformly chosen position below `Q` is right with at least
`1 / Q` of that probability, since it cannot recognize the right entry. This is the guessing step
of [BonehShoup2023] in Section 21.11.4 (p. 908), where the list is the adversary's random-oracle
queries and the book states only a "non-negligible (though smaller)" chance, and in the proof of
Theorem 11.4 (Section 11.5.1, pp. 446–448), where it is the source of the factor `Q`: choosing one
of at most `Q` queries at random gives `CDHadv[Bcdh, G] ≥ Pr[Z] / Q`, equation (11.12).

The reduction `listCDHToCDH` takes its index sampler as an argument, and the analysis is general
in its law: `eval_listCDHExperiment_le_mul_add_of_index` bounds the list experiment by `c` times the
CDH experiment of `listCDHToCDH` plus `ε` for every index sampler such that, for each of the first
`Q` entries of every list, `c` times the probability of selecting it, plus `ε`, is at least `1`;
`eval_listCDHExperiment_le_mul` is its case `ε = 0`. An exactly uniform index below `Q` gives
`c = Q` and `ε = 0` (`listCDHAdvantage_le_mul_cdhAdvantage`). A machine with fair coins cannot draw
an exactly uniform index below every `Q`. It can draw `Cslib.ProbComp.sampleModIndex width Q`: the
residue modulo `Q` of a number written with `width` fair coins, capped at `Q` (which matters only
at `Q = 0`). Each position below `Q` is drawn with probability at least `1 / Q - 1 / 2 ^ width`
(`Cslib.ProbComp.one_le_mul_eval_sampleModNat_add`), so the reduction keeps the factor `Q` and
adds the term `Q / 2 ^ width` (`eval_listCDHExperiment_le_mul_add`), for every `width` and every
`Q`. The efficient reduction over a prime-order group family draws its index this way; it, its
certificate, its bound and the conclusion under the CDH assumption are in
`CslibFrontier/Crypto/Computational/DiffieHellman/ListCDHFamily.lean`.

No hypothesis restricts `Q` or the adversary's lists:

* At `Q = 0` the list experiment is never won (`listCDHAdvantage_zero`), and both bounds read
  `0 ≤ 0`. The exact bound's index is then uniform below `1`, and `sampleModIndex width 0` always
  returns `0`, so the reduction reads position `0`.
* A list shorter than `Q` counts in full, since `l.take Q = l`; an exactly uniform index falls past
  its end with probability `1 - l.length / Q`, and the reduction then outputs `g`.
* Repeated entries are allowed. Each copy of the Diffie–Hellman value among the first `Q` entries
  adds `1 / Q` to the reduction's success probability, so the bound can be strict.

Differences from the book:

* Groups are written additively, and the experiment draws exponents, as in
  `Cslib.Crypto.cdhExperiment`.
* The book's list is built from the adversary's random-oracle queries: in Theorem 11.4 all of
  them, at most `Q`; in Section 21.11.4 those of the form `(pw', id_P, id_Q, u, v, w')`, with no
  stated bound. Here the adversary returns the list, and only its first `Q` entries count, so an
  adversary that returns more entries gains nothing from them.
* The book's solver chooses uniformly among the queries it collected (in Theorem 11.4, the points
  of `Domain(Map)`, at most `Q` of them) and outputs "failure" when there are none. This reduction
  draws a position below `Q` without looking at the list, and outputs `g` when the position is past
  the end; any fixed element would do. Each member of the first `Q` entries is still chosen with
  probability at least `1 / Q`.
* The win condition is decided, so the experiment takes `[DecidableEq G]`, as
  `Cslib.Crypto.cdhExperiment` does.

The book names neither the problem nor the reduction: "list CDH" and the names of all
declarations here are this library's names.

## Main definitions

* `Cslib.Crypto.listCDHExperiment`, `Cslib.Crypto.listCDHAdvantage`: the list form of CDH and its
  success probability.
* `Cslib.Crypto.listCDHToCDH`: the reduction, for a given index sampler.

## Main results

* `Cslib.Crypto.listCDHAdvantage_zero`: at `Q = 0` the list experiment is never won.
* `Cslib.Crypto.eval_listCDHExperiment_le_mul_add_of_index`,
  `Cslib.Crypto.eval_listCDHExperiment_le_mul`: the bound for a general index sampler, with and
  without an additive term.
* `Cslib.Crypto.listCDHAdvantage_le_mul_cdhAdvantage`: the list advantage is at most `Q` times the
  CDH advantage of the reduction with an exactly uniform index, for every `Q`.
* `Cslib.Crypto.eval_listCDHExperiment_le_mul_add`: with the fair-coin index
  `sampleModIndex width Q`, the list success probability is at most `Q` times the CDH success
  probability of the reduction plus `Q / 2 ^ width`, for every `width` and every `Q`.
* `Cslib.Crypto.eval_listCDHExperiment_mono`: the list success probability does not decrease when
  the bound `Q` grows.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 21.11.4, p. 908, and Section 11.5.1, Theorem 11.4 and its
  proof with equation (11.12), pp. 446–448.
-/

public section

namespace Cslib.Crypto

open Probability
open scoped ENNReal NNReal

section Experiments

variable {G : Type} [AddCommGroup G] (q : ℕ) [Module (ZMod q) G] (g : G)

/-- The guessing reduction of [BonehShoup2023], Section 21.11.4 (p. 908) and the proof of
Theorem 11.4 (p. 447), with its index sampler `index`: on the CDH instance `(s, t)`, run the list
adversary, draw a position from `index` and return the entry there, or `g` when the position is
past the end of the list. -/
@[expose] def listCDHToCDH (index : ProbComp ℕ) (A : G → G → ProbComp (List G)) (s t : G) :
    ProbComp G := do
  let l ← A s t
  let i ← index
  return l.getD i g

variable [NeZero q] [DecidableEq G]

/-- The list form of CDH in the group generated by `g`: the challenger draws uniform exponents `a`
and `b` and gives the adversary `a • g` and `b • g`; the adversary wins when `(a * b) • g` is among
the first `Q` entries of its list. The name is this library's. -/
@[expose] noncomputable def listCDHExperiment (Q : ℕ) (A : G → G → ProbComp (List G)) :
    Experiment := do
  let a ← $ᵗ ZMod q
  let b ← $ᵗ ZMod q
  let l ← A (a • g) (b • g)
  return (a * b) • g ∈ l.take Q

/-- The success probability of `A` in `listCDHExperiment`. -/
@[expose] noncomputable def listCDHAdvantage (Q : ℕ) (A : G → G → ProbComp (List G)) : ℝ≥0 :=
  Experiment.succProbability (listCDHExperiment q g Q A)

/-- **At `Q = 0` the list form of CDH is never won**: no entry is among the first `0`. -/
theorem listCDHAdvantage_zero (A : G → G → ProbComp (List G)) :
    listCDHAdvantage q g 0 A = 0 := by
  have hfalse (p : PMF (List G)) : p.map (fun _ => false) = PMF.pure false := PMF.map_const p false
  simp [listCDHAdvantage, listCDHExperiment, Experiment.succProbability, hfalse,
    Game.succProbability]

/-- **The guessing step for a general index sampler, with an additive term**: if, for every list
`l` and every member `x` of `l.take Q`, `c` times the probability that the entry of `l` at a
position drawn from `index` (or `g` past the end) is `x`, plus `ε`, is at least `1`, then the list
experiment accepts with probability at most `c` times that of the CDH experiment for
`listCDHToCDH`, plus `ε`. The hypothesis is on the index law alone. -/
theorem eval_listCDHExperiment_le_mul_add_of_index (Q : ℕ) (index : ProbComp ℕ) {c ε : ℝ≥0∞}
    (hindex : ∀ (l : List G) (x : G), x ∈ l.take Q →
      1 ≤ c * (ProbComp.eval index).map (fun i => l.getD i g) x + ε)
    (A : G → G → ProbComp (List G)) :
    ProbComp.eval (listCDHExperiment q g Q A) true ≤
      c * ProbComp.eval (cdhExperiment q g (listCDHToCDH g index A)) true + ε := by
  simp only [listCDHExperiment, cdhExperiment, listCDHToCDH, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  refine PMF.bind_apply_le_mul_bind_apply_add _ fun a => ?_
  refine PMF.bind_apply_le_mul_bind_apply_add _ fun b => ?_
  refine PMF.bind_apply_le_mul_bind_apply_add _ fun l => ?_
  have hmap : ((ProbComp.eval index).bind fun i => PMF.pure (decide (l.getD i g = (a * b) • g))) =
      ((ProbComp.eval index).map fun i => l.getD i g).bind
        fun z => PMF.pure (decide (z = (a * b) • g)) := by
    rw [PMF.bind_map]
    rfl
  rw [hmap, PMF.bind_pure_decide_eq_apply_true']
  by_cases hx : (a * b) • g ∈ l.take Q
  · simpa [hx] using hindex l _ hx
  · simp [hx]

/-- **The guessing step for a general index sampler**: if, for every list `l`, the entry of `l` at
a position drawn from `index` (or `g` past the end) is each member of `l.take Q` with probability
at least `1 / c`, then the list experiment accepts with probability at most `c` times that of the
CDH experiment for `listCDHToCDH`. The hypothesis is on the index law alone. This is the case
`ε = 0` of `eval_listCDHExperiment_le_mul_add_of_index`. -/
theorem eval_listCDHExperiment_le_mul (Q : ℕ) (index : ProbComp ℕ) {c : ℝ≥0∞}
    (hindex : ∀ (l : List G) (x : G), x ∈ l.take Q →
      1 ≤ c * (ProbComp.eval index).map (fun i => l.getD i g) x)
    (A : G → G → ProbComp (List G)) :
    ProbComp.eval (listCDHExperiment q g Q A) true ≤
      c * ProbComp.eval (cdhExperiment q g (listCDHToCDH g index A)) true := by
  simpa using eval_listCDHExperiment_le_mul_add_of_index q g Q index (ε := 0)
    (fun l x hx => by simpa using hindex l x hx) A

/-- **The list form of CDH loses at most a factor `Q`** ([BonehShoup2023], Section 21.11.4, p. 908,
and equation (11.12) in the proof of Theorem 11.4, p. 448): the guessing reduction with the index
`Fin.val <$> ProbComp.unifFin (Q - 1)`, exactly uniform below `Q` when `0 < Q`, solves CDH with at
least `1 / Q` of the list adversary's success probability. It holds for every `Q`, including `0`,
every list length and lists with repeated entries; beyond `NeZero q` and `DecidableEq G`, which the
experiments need, there is no hypothesis on `q` or `g`. With the fair-coin index
`ProbComp.sampleModIndex width Q` the factor stays `Q` and the term `Q / 2 ^ width` is added
(`eval_listCDHExperiment_le_mul_add`). -/
theorem listCDHAdvantage_le_mul_cdhAdvantage (Q : ℕ) (A : G → G → ProbComp (List G)) :
    listCDHAdvantage q g Q A ≤
      Q * cdhAdvantage q g (listCDHToCDH g (Fin.val <$> ProbComp.unifFin (Q - 1)) A) := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · simp [listCDHAdvantage_zero]
  obtain ⟨Q, rfl⟩ : ∃ m, Q = m + 1 := ⟨Q - 1, (Nat.sub_add_cancel hQ).symm⟩
  have hle := eval_listCDHExperiment_le_mul q g (Q + 1) (Fin.val <$> ProbComp.unifFin Q)
    (c := ((Q + 1 : ℕ) : ℝ≥0∞)) (fun l x hx => by
      rw [ProbComp.eval_map, ProbComp.eval_unifFin, PMF.map_comp]
      calc (1 : ℝ≥0∞) = ((Q + 1 : ℕ) : ℝ≥0∞) * ((Q + 1 : ℕ) : ℝ≥0∞)⁻¹ :=
            (ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)).symm
        _ ≤ _ := mul_le_mul' le_rfl (PMF.inv_le_map_uniformOfFintype_getD g hx)) A
  rw [Nat.add_sub_cancel]
  unfold listCDHAdvantage cdhAdvantage
  simp only [Experiment.succProbability, Game.succProbability]
  rw [← ENNReal.toNNReal_natCast, ← ENNReal.toNNReal_mul]
  exact ENNReal.toNNReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _))
    hle

/-- **The guessing step with a fair-coin index loses a factor `Q` plus `Q / 2 ^ width`**: the
guessing reduction of [BonehShoup2023], Section 21.11.4 (p. 908) and equation (11.12) in the proof
of Theorem 11.4 (p. 448), run with the index `ProbComp.sampleModIndex width Q` drawn from `width`
fair coins, solves CDH with probability at least `1 / Q` of the list adversary's success
probability, minus `1 / 2 ^ width`. The book draws the index exactly uniformly; the fair-coin index
and the term `Q / 2 ^ width` are this library's. The factor is exactly `Q`: each position below
`Q` is drawn with probability at least `1 / Q - 1 / 2 ^ width`
(`ProbComp.one_le_mul_eval_sampleModNat_add`), so whenever the Diffie–Hellman value is among the
first `Q` entries the reduction returns it with at least that probability. It holds for every
`width` and every `Q`, including `Q = 0`, where both sides are `0`; beyond `NeZero q` and
`DecidableEq G` there is no hypothesis on `q` or `g`. -/
theorem eval_listCDHExperiment_le_mul_add (width Q : ℕ) (A : G → G → ProbComp (List G)) :
    ProbComp.eval (listCDHExperiment q g Q A) true ≤
      Q * ProbComp.eval
          (cdhExperiment q g (listCDHToCDH g (ProbComp.sampleModIndex width Q) A)) true +
        Q / 2 ^ width := by
  refine eval_listCDHExperiment_le_mul_add_of_index q g Q _ (fun l x hx => ?_) A
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  rw [List.length_take] at hi
  have hiQ : i < Q := hi.trans_le (min_le_left _ _)
  have hil : i < l.length := hi.trans_le (min_le_right _ _)
  rw [ProbComp.sampleModIndex_eq_sampleModNat width ((Nat.zero_le i).trans_lt hiQ)]
  calc (1 : ℝ≥0∞) ≤ Q * ProbComp.eval (ProbComp.sampleModNat width Q) i + Q / 2 ^ width :=
        ProbComp.one_le_mul_eval_sampleModNat_add hiQ
    _ ≤ _ := by
        gcongr
        have hget : (l.take Q)[i] = l.getD i g := by
          simp [List.getElem_take, List.getD_eq_getElem?_getD, hil]
        rw [hget]
        exact PMF.le_map_apply _ (fun j => l.getD j g) i

/-- **More entries that count cannot hurt the adversary**: if `Q ≤ Q'`, the list experiment with
bound `Q'` accepts with probability at least that with bound `Q`, since the first `Q` entries of a
list are among its first `Q'`. -/
theorem eval_listCDHExperiment_mono {Q Q' : ℕ} (hle : Q ≤ Q') (A : G → G → ProbComp (List G)) :
    ProbComp.eval (listCDHExperiment q g Q A) true ≤
      ProbComp.eval (listCDHExperiment q g Q' A) true := by
  simp only [listCDHExperiment, ProbComp.eval_bind, ProbComp.eval_pure]
  refine PMF.bind_apply_mono_on_support _ _ fun a _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun b _ => ?_
  refine PMF.bind_apply_mono_on_support _ _ fun l _ => ?_
  by_cases hx : (a * b) • g ∈ l.take Q
  · simp [hx, List.take_subset_take_left l hle hx]
  · simp [hx]

end Experiments

end Cslib.Crypto
