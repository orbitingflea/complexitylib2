/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.ProductConditioning
import Complexity.Probability.Divergence
import Complexity.Probability.PMF.Event
import Complexity.Probability.PMF.Expect
import Complexity.Probability.PMF.Map
public import Complexity.Probability.Conditioning
import Complexity.Probability.StatisticalDistance
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Conditioning a product distribution with side information

Raz's conditioning lemma (`Cslib.Probability.PMF.sum_sq_dist_map_filter_pi_le`) conditions a
product distribution on an event about its coordinates. Holenstein applies it to events that also
involve side information: a pair `(u, v)` drawn from a joint distribution whose first marginal is a
product `pi p`, and an event `W` about the pair. The conditioned marginal of `u` still has
divergence at most `ln (1 / Pr[W])` from `pi p`, because its masses are at most those of `pi p`
divided by `Pr[W]` (`sum_mul_log_div_le_log_of_le`), so the coordinates move by
`∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2` (`sum_sq_dist_map_filter_le`)
[Holenstein, proof of Corollary 6][Holenstein2009].

**Holenstein's Corollary 6** (`sum_dist_filter_sideJoint_le`) lets the coordinates be independent
only given a further random variable `t`, and lets the side information `v` depend on `t` and `u`:
with `t ~ μ` and `(u, v) ~ J t`, where the first marginal of `J t` is the product `pi (K · t)`,
`∑ⱼ ‖P_{TV Uⱼ | W} - P_{TV | W} P_{Uⱼ | T}‖ ≤ √(k · ln (|V| / Pr[W]) / 2)`. Revealing `(t, v)` turns
each distance into an average of conditional distances (`dist_map_pair_bind_eq`); given `(t, v)`,
the law of `u` is that of `J t` conditioned on the slice of `W` at `(t, v)`
(`conditionalSnd_filter_sideJoint`), so the lemma above applies; and Jensen's inequality for the
square root and the logarithm combines the slices. Holenstein uses the support `V*` of `v` under
`W` where this statement uses the whole alphabet `V`, which can only make the bound here weaker;
the factor `1 / 2` from Pinsker's inequality in nats makes it stronger, since
`ln x / 2 ≤ log₂ x` for `x ≥ 1`.

## Main definitions

* `Cslib.Probability.PMF.sideJoint`: the law of `((t, v), u)`.

## Main results

* `Cslib.Probability.PMF.sum_mul_log_div_le_log_of_le`: divergence of a distribution dominated by
  a multiple of another.
* `Cslib.Probability.PMF.sum_sq_dist_map_filter_le`: Raz's conditioning lemma with side
  information.
* `Cslib.Probability.PMF.dist_map_pair_bind_eq`: distance after revealing a first component.
* `Cslib.Probability.PMF.sum_dist_filter_sideJoint_le`: Holenstein's Corollary 6.

## References

* [T. Holenstein, *Parallel repetition: simplifications and the no-signaling case*][Holenstein2009]
-/

@[expose] public section

namespace Cslib.Probability.PMF

open Finset
open scoped Cslib.Probability.PMF

variable {α : Type*} [Fintype α]

/-- If the masses of `p` are at most those of `q` divided by `c > 0`, the divergence of `p` from
`q` is at most `ln (1 / c)`. -/
theorem sum_mul_log_div_le_log_of_le {p q : PMF α} {c : ℝ} (hc : 0 < c)
    (h : ∀ a, (p a).toReal ≤ (q a).toReal / c) :
    ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal) ≤ Real.log (1 / c) := by
  calc ∑ a, (p a).toReal * Real.log ((p a).toReal / (q a).toReal)
      ≤ ∑ a, (p a).toReal * Real.log (1 / c) := by
        refine sum_le_sum fun a _ => ?_
        have hp := ENNReal.toReal_nonneg (a := p a)
        rcases hp.eq_or_lt with hp0 | hp0
        · rw [← hp0]
          simp
        have hq : 0 < (q a).toReal := by
          have := h a
          rw [le_div_iff₀ hc] at this
          nlinarith
        refine mul_le_mul_of_nonneg_left (Real.log_le_log (div_pos hp0 hq) ?_) hp
        rw [div_le_div_iff₀ hq hc, one_mul]
        have := h a
        rw [le_div_iff₀ hc] at this
        linarith
    _ = Real.log (1 / c) := by rw [← sum_mul, sum_toReal, one_mul]

section Product

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)] {V : Type*} [Finite V]

/-- **Raz's conditioning lemma with side information** [Holenstein, proof of
Corollary 6][Holenstein2009]. Let `(u, v)` be drawn from a joint distribution `J` whose first
marginal is the product `pi p`, and let `W` be an event about `(u, v)`. Conditioned on `W`, the
coordinates of `u` move by `∑ⱼ ‖P_{Uⱼ | W} - P_{Uⱼ}‖² ≤ ln (1 / Pr[W]) / 2`. -/
theorem sum_sq_dist_map_filter_le (p : ∀ i, PMF (β i)) (J : PMF ((∀ i, β i) × V))
    (hJ : J.map Prod.fst = pi p) (W : Set ((∀ i, β i) × V)) (hW : ∃ x ∈ W, x ∈ J.support) :
    ∑ j, dist ((J.filter W hW).map fun x => x.1 j) (p j) ^ 2 ≤
      Real.log (1 / (J.toOuterMeasure W).toReal) / 2 := by
  classical
  have := Fintype.ofFinite V
  set w := (J.toOuterMeasure W).toReal
  have hw : 0 < w := (toOuterMeasure_toReal_pos_iff J W).mpr hW
  set Q := (J.filter W hW).map Prod.fst
  have hmap : ∀ j, (J.filter W hW).map (fun x => x.1 j) = Q.map fun u => u j := fun j => by
    rw [PMF.map_comp]
    rfl
  -- The conditioned marginal is dominated by `pi p / Pr[W]`.
  have hdom : ∀ u, (Q u).toReal ≤ ((pi p) u).toReal / w := by
    intro u
    rw [← hJ, map_apply_toReal, map_apply_toReal, sum_div]
    refine sum_le_sum fun x _ => ?_
    rw [filter_apply_toReal]
    split_ifs <;> first | exact le_rfl | exact div_nonneg ENNReal.toReal_nonneg hw.le | simp
  have hQ : Q.support ⊆ (pi p).support := by
    intro u hu
    have hpos : 0 < (Q u).toReal := ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hu)
      (PMF.apply_ne_top _ _)
    have := hdom u
    have hpu : 0 < ((pi p) u).toReal := by
      have := (lt_of_lt_of_le hpos this)
      exact (div_pos_iff_of_pos_right hw).mp this
    exact (PMF.mem_support_iff _ _).mpr fun h => by simp [h] at hpu
  have hsup := sum_sum_mul_log_div_map_le Q p hQ
  have hkl := sum_mul_log_div_le_log_of_le hw hdom
  have hpinsker : ∀ j, 2 * dist (Q.map fun u => u j) (p j) ^ 2 ≤
      ∑ a, ((Q.map fun u => u j) a).toReal *
        Real.log (((Q.map fun u => u j) a).toReal / (p j a).toReal) := by
    intro j
    refine two_mul_dist_sq_le_sum_mul_log_div fun a ha => ?_
    rw [PMF.support_map] at ha
    obtain ⟨u, hu, rfl⟩ := ha
    exact (mem_support_pi_iff p u).mp (hQ hu) j
  have := sum_le_sum fun j (_ : j ∈ univ) => hpinsker j
  rw [← mul_sum] at this
  simp only [hmap]
  linarith

end Product

section Decomposition

variable {S X Y : Type*} [Fintype S] [Fintype Y]

/-- Revealing the first component: the distance of `(s, f x)` from `(s, y)` with `y` drawn from
`K s` is the average over `s` of the distance of the conditional law of `f x` from `K s`. -/
theorem dist_map_pair_bind_eq (Q : PMF (S × X)) (f : X → Y) (K : S → PMF Y) :
    dist (Q.map fun z => (z.1, f z.2)) ((Q.map Prod.fst).bind fun s => (K s).map (s, ·)) =
      ∑ s, ((Q.map Prod.fst) s).toReal * dist ((conditionalSnd Q s).map f) (K s) := by
  nth_rewrite 1 [← bind_conditionalSnd Q]
  rw [PMF.map_bind]
  have : ∀ s, ((conditionalSnd Q s).map (s, ·)).map (fun z => (z.1, f z.2)) =
      ((conditionalSnd Q s).map f).map (s, ·) := fun s => by
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  simp only [this]
  exact dist_bind_pair (Q.map Prod.fst) (fun s => (conditionalSnd Q s).map f) K

end Decomposition

section Corollary

variable {ι : Type*} [Fintype ι] {β : ι → Type*} [∀ i, Fintype (β i)] {T V : Type*} [Fintype T]
  [Fintype V]

/-- The joint law of `((t, v), u)`: `t` drawn from `μ`, then `(u, v)` from `J t`. -/
noncomputable def sideJoint (μ : PMF T) (J : T → PMF ((∀ i, β i) × V)) :
    PMF ((T × V) × (∀ i, β i)) :=
  μ.bind fun t => (J t).map fun x => ((t, x.2), x.1)

omit [Fintype ι] [∀ i, Fintype (β i)] [Fintype T] [Fintype V] in
theorem sideJoint_apply (μ : PMF T) (J : T → PMF ((∀ i, β i) × V)) (t : T) (v : V)
    (u : ∀ i, β i) : (sideJoint μ J) ((t, v), u) = μ t * (J t) (u, v) := by
  classical
  rw [sideJoint, PMF.bind_apply, tsum_eq_single t]
  · rw [PMF.map_apply, tsum_eq_single (u, v)]
    · simp
    · intro x hx
      rw [ite_eq_right]
      intro h
      exact hx (Prod.ext (congrArg Prod.snd h).symm (congrArg (·.2) (congrArg Prod.fst h)).symm)
  · intro t' ht'
    rw [PMF.map_apply]
    refine mul_eq_zero_of_right _ (ENNReal.tsum_eq_zero.mpr fun x => ite_eq_right fun h => ?_)
    exact absurd (congrArg (·.1) (congrArg Prod.fst h)) (Ne.symm ht')

/-- The pairs `(u, v)` that complete `(t, v)` to an outcome in `W`. -/
def sliceEvent (W : Set ((T × V) × (∀ i, β i))) (t : T) (v : V) : Set ((∀ i, β i) × V) :=
  {x | x.2 = v ∧ ((t, v), x.1) ∈ W}

omit [Fintype T] [Fintype V] in
open Classical in
theorem toOuterMeasure_sliceEvent_toReal [Finite V] (J : T → PMF ((∀ i, β i) × V))
    (W : Set ((T × V) × (∀ i, β i))) (t : T) (v : V) :
    ((J t).toOuterMeasure (sliceEvent W t v)).toReal =
      ∑ u, if ((t, v), u) ∈ W then ((J t) (u, v)).toReal else 0 := by
  have := Fintype.ofFinite V
  rw [toOuterMeasure_apply_toReal, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_eq_single v]
  · by_cases h : ((t, v), u) ∈ W <;> simp [sliceEvent, h]
  · intro v' _ hv'
    simp [sliceEvent, hv']
  · simp

omit [Fintype ι] [∀ i, Fintype (β i)] [Fintype T] [Fintype V] in
open Classical in
/-- The probability of `(t, v)` after conditioning on `W` is `μ t · Pr_{J t}[W_{t,v}] / Pr[W]`. -/
theorem map_fst_filter_sideJoint_toReal [Finite ι] [∀ i, Finite (β i)] [Finite T] [Finite V]
    (μ : PMF T) (J : T → PMF ((∀ i, β i) × V))
    (W : Set ((T × V) × (∀ i, β i))) (hW : ∃ x ∈ W, x ∈ (sideJoint μ J).support) (t : T)
    (v : V) :
    ((((sideJoint μ J).filter W hW).map Prod.fst) (t, v)).toReal =
      (μ t).toReal * ((J t).toOuterMeasure (sliceEvent W t v)).toReal /
        ((sideJoint μ J).toOuterMeasure W).toReal := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (β i)
  have := Fintype.ofFinite T
  have := Fintype.ofFinite V
  rw [map_apply_toReal, Fintype.sum_prod_type, Finset.sum_eq_single (t, v),
    toOuterMeasure_sliceEvent_toReal, Finset.mul_sum, Finset.sum_div]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [ite_eq_left rfl, filter_apply_toReal, sideJoint_apply, ENNReal.toReal_mul]
    split_ifs <;> ring
  · intro s _ hs
    exact Finset.sum_eq_zero fun u _ => ite_eq_right fun h => absurd h.symm hs
  · simp

omit [Fintype ι] [∀ i, Fintype (β i)] [Fintype T] [Fintype V] in
open Classical in
/-- Given `(t, v)`, the law of `u` conditioned on `W` is the law of `u` under `J t` conditioned on
the slice `W_{t,v}`. -/
theorem conditionalSnd_filter_sideJoint [Finite ι] [∀ i, Finite (β i)] [Finite T] [Finite V]
    (μ : PMF T) (J : T → PMF ((∀ i, β i) × V))
    (W : Set ((T × V) × (∀ i, β i))) (hW : ∃ x ∈ W, x ∈ (sideJoint μ J).support) (t : T) (v : V)
    (hs : (t, v) ∈ (((sideJoint μ J).filter W hW).map Prod.fst).support)
    (hWs : ∃ x ∈ sliceEvent W t v, x ∈ (J t).support) :
    conditionalSnd ((sideJoint μ J).filter W hW) (t, v) =
      ((J t).filter (sliceEvent W t v) hWs).map Prod.fst := by
  have := Fintype.ofFinite ι
  have := fun i => Fintype.ofFinite (β i)
  have := Fintype.ofFinite T
  have := Fintype.ofFinite V
  set Pw := ((sideJoint μ J).toOuterMeasure W).toReal
  set c := ((J t).toOuterMeasure (sliceEvent W t v)).toReal
  have hPw : 0 < Pw := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  have hc : 0 < c := (toOuterMeasure_toReal_pos_iff _ _).mpr hWs
  have hw := map_fst_filter_sideJoint_toReal μ J W hW t v
  have hwpos : 0 < ((((sideJoint μ J).filter W hW).map Prod.fst) (t, v)).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp hs) (PMF.apply_ne_top _ _)
  have hμ : 0 < (μ t).toReal := by
    rw [hw] at hwpos
    have := ENNReal.toReal_nonneg (a := μ t)
    rcases this.eq_or_lt with h | h
    · rw [← h] at hwpos
      simp at hwpos
    · exact h
  ext u
  rw [← ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    conditionalSnd_apply _ _ hs u, ENNReal.toReal_div, hw, filter_apply_toReal, sideJoint_apply,
    ENNReal.toReal_mul, map_apply_toReal, Fintype.sum_prod_type, Finset.sum_eq_single u]
  · rw [Finset.sum_eq_single v]
    · rw [ite_eq_left rfl, filter_apply_toReal]
      by_cases h : ((t, v), u) ∈ W
      · rw [ite_eq_left h, ite_eq_left (show (u, v) ∈ sliceEvent W t v from ⟨rfl, h⟩)]
        field_simp
        rw [div_eq_div_iff (mul_pos hPw hc).ne' hc.ne']
        ring
      · rw [ite_eq_right h, ite_eq_right (show (u, v) ∉ sliceEvent W t v from fun h' => h h'.2)]
        simp
    · intro v' _ hv'
      rw [ite_eq_left rfl, filter_apply_toReal,
        ite_eq_right (show (u, v') ∉ sliceEvent W t v from fun h' => hv' h'.1)]
    · simp
  · intro u' _ hu'
    exact Finset.sum_eq_zero fun v' _ => ite_eq_right fun h => hu' h.symm
  · simp

/-- **Holenstein's Corollary 6** [Holenstein, Corollary 6][Holenstein2009], with the alphabet of
`V` in place of its support under `W` and the divergence in nats. Draw `t` from `μ`, then the
coordinates `u_i` independently from `K i t` together with side information `v`
(`(J t).map Prod.fst = pi (K · t)`), and condition on an event `W`. Then sampling each coordinate
from `K j t` instead, ignoring `W` and `v`, changes the law of `((t, v), u_j)` little on average:
`∑ⱼ ‖P_{TV Uⱼ | W} - P_{TV | W} P_{Uⱼ | T}‖ ≤ √(k · ln (|V| / Pr[W]) / 2)`. -/
theorem sum_dist_filter_sideJoint_le (μ : PMF T) (K : ∀ i, T → PMF (β i))
    (J : T → PMF ((∀ i, β i) × V)) (hJ : ∀ t, (J t).map Prod.fst = pi fun i => K i t)
    (W : Set ((T × V) × (∀ i, β i))) (hW : ∃ x ∈ W, x ∈ (sideJoint μ J).support) :
    ∑ j, dist (((sideJoint μ J).filter W hW).map fun z => (z.1, z.2 j))
        ((((sideJoint μ J).filter W hW).map Prod.fst).bind fun s => (K j s.1).map (s, ·)) ≤
      Real.sqrt (Fintype.card ι *
        Real.log (Fintype.card V / ((sideJoint μ J).toOuterMeasure W).toReal) / 2) := by
  classical
  set Q := (sideJoint μ J).filter W hW
  set Pw := ((sideJoint μ J).toOuterMeasure W).toReal
  have hPw : 0 < Pw := (toOuterMeasure_toReal_pos_iff _ W).mpr hW
  set w : T × V → ℝ := fun s => ((Q.map Prod.fst) s).toReal
  set c : T × V → ℝ := fun s => ((J s.1).toOuterMeasure (sliceEvent W s.1 s.2)).toReal
  set k : ℝ := (Fintype.card ι : ℝ)
  have hw : ∀ s, w s = (μ s.1).toReal * c s / Pw := fun s =>
    map_fst_filter_sideJoint_toReal μ J W hW s.1 s.2
  have hw0 : ∀ s, 0 ≤ w s := fun s => ENNReal.toReal_nonneg
  have hwsum : ∑ s, w s = 1 := sum_toReal _
  have hc1 : ∀ s, c s ≤ 1 := fun s => by
    simpa using ENNReal.toReal_mono ENNReal.one_ne_top (toOuterMeasure_le_one _ _)
  -- Per point bound.
  set B : T × V → ℝ := fun s => k * Real.log (1 / c s) / 2
  have hB0 : ∀ s, 0 ≤ B s := fun s => by
    have : 0 ≤ Real.log (1 / c s) := by
      rcases (show 0 ≤ c s from ENNReal.toReal_nonneg).eq_or_lt with h | h
      · rw [← h]
        simp
      · exact Real.log_nonneg (by rw [le_div_iff₀ h]; linarith [hc1 s])
    positivity
  have hpoint : ∀ s, w s * ∑ j, dist ((conditionalSnd Q s).map fun u => u j) (K j s.1) ≤
      w s * Real.sqrt (B s) := by
    intro s
    rcases (hw0 s).eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    refine mul_le_mul_of_nonneg_left ?_ (hw0 s)
    have hcpos : 0 < c s := by
      rw [hw] at hpos
      by_contra hc
      have : c s = 0 := le_antisymm (not_lt.mp hc) ENNReal.toReal_nonneg
      rw [this] at hpos
      simp at hpos
    have hs : s ∈ (Q.map Prod.fst).support := by
      refine (PMF.mem_support_iff _ _).mpr fun h => ?_
      have : w s = 0 := by simp only [w, h, ENNReal.toReal_zero]
      linarith
    have hWs : ∃ x ∈ sliceEvent W s.1 s.2, x ∈ (J s.1).support :=
      (toOuterMeasure_toReal_pos_iff _ _).mp hcpos
    have hcond := conditionalSnd_filter_sideJoint μ J W hW s.1 s.2 hs hWs
    have hside := sum_sq_dist_map_filter_le (fun i => K i s.1) (J s.1) (hJ s.1) _ hWs
    have hmap : ∀ j, (conditionalSnd Q s).map (fun u => u j) =
        ((J s.1).filter (sliceEvent W s.1 s.2) hWs).map fun x => x.1 j := fun j => by
      rw [hcond, PMF.map_comp]
      rfl
    simp only [hmap]
    refine Real.le_sqrt_of_sq_le ?_
    have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j => dist (((J s.1).filter (sliceEvent W s.1 s.2) hWs).map fun x => x.1 j)
        (K j s.1))
    rw [Finset.card_univ] at hcs
    calc _ ≤ _ := hcs
      _ ≤ k * (Real.log (1 / c s) / 2) := mul_le_mul_of_nonneg_left hside (by positivity)
      _ = B s := by ring
  -- Positive weights force positive slice probabilities.
  have hcpos : ∀ s, 0 < w s → 0 < c s := fun s hpos => by
    rw [hw] at hpos
    by_contra hc
    have : c s = 0 := le_antisymm (not_lt.mp hc) ENNReal.toReal_nonneg
    rw [this] at hpos
    simp at hpos
  set S := Finset.univ.filter fun s : T × V => 0 < w s
  have hsub : ∀ f : T × V → ℝ, (∀ s, w s = 0 → f s = 0) → ∑ s, f s = ∑ s ∈ S, f s := by
    intro f hf
    refine (Finset.sum_subset (Finset.subset_univ _) fun s _ hs => hf s ?_).symm
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hs
    exact le_antisymm hs (hw0 s)
  have hwS : ∑ s ∈ S, w s = 1 := by
    rw [← hsub w fun s h => h]
    exact hwsum
  -- Jensen for the logarithm on the positive weights.
  have hjensen : ∑ s ∈ S, w s * Real.log (1 / c s) ≤ Real.log (∑ s ∈ S, w s * (1 / c s)) := by
    have := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := S) (w := w)
      (p := fun s => 1 / c s) (fun s _ => hw0 s) hwS fun s hs => by
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        exact one_div_pos.mpr (hcpos s hs)
    simpa only [smul_eq_mul] using this
  have hratio : ∑ s ∈ S, w s * (1 / c s) ≤ Fintype.card V / Pw := by
    calc ∑ s ∈ S, w s * (1 / c s) = ∑ s ∈ S, (μ s.1).toReal / Pw := by
          refine Finset.sum_congr rfl fun s hs => ?_
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
          rw [hw]
          field_simp [(hcpos s hs).ne']
      _ ≤ ∑ s : T × V, (μ s.1).toReal / Pw := by
          refine Finset.sum_le_sum_of_subset_of_nonneg (f := fun s : T × V => (μ s.1).toReal / Pw)
            (Finset.subset_univ S) fun s _ _ => ?_
          exact div_nonneg ENNReal.toReal_nonneg hPw.le
      _ = Fintype.card V / Pw := by
          rw [← Finset.sum_div, Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum, sum_toReal, mul_one]
  have hratio_pos : 0 < ∑ s ∈ S, w s * (1 / c s) := by
    have hne : S.Nonempty := by
      by_contra h
      rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hwS
      exact zero_ne_one hwS
    refine Finset.sum_pos (fun s hs => ?_) hne
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hs
    exact mul_pos hs (one_div_pos.mpr (hcpos s hs))
  have hkey : ∑ s, w s * B s ≤ k * Real.log (Fintype.card V / Pw) / 2 := by
    rw [hsub (fun s => w s * B s) fun s h => by simp [h]]
    calc ∑ s ∈ S, w s * B s = k / 2 * ∑ s ∈ S, w s * Real.log (1 / c s) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          simp only [B]
          ring
      _ ≤ k / 2 * Real.log (Fintype.card V / Pw) := by
          gcongr
          exact hjensen.trans (Real.log_le_log hratio_pos hratio)
      _ = _ := by ring
  -- Jensen for the square root.
  have hsqrt : ∑ s, w s * Real.sqrt (B s) ≤ Real.sqrt (∑ s, w s * B s) := by
    have := (Real.strictConcaveOn_sqrt).concaveOn.le_map_sum (t := Finset.univ) (w := w)
      (p := B) (fun s _ => hw0 s) hwsum fun s _ => Set.mem_Ici.mpr (hB0 s)
    simpa only [smul_eq_mul] using this
  calc ∑ j, dist (Q.map fun z => (z.1, z.2 j)) ((Q.map Prod.fst).bind fun s => (K j s.1).map (s, ·))
      = ∑ j, ∑ s, w s * dist ((conditionalSnd Q s).map fun u => u j) (K j s.1) :=
        Finset.sum_congr rfl fun j _ =>
          dist_map_pair_bind_eq Q (fun u => u j) fun s => K j s.1
    _ = ∑ s, w s * ∑ j, dist ((conditionalSnd Q s).map fun u => u j) (K j s.1) := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ∑ s, w s * Real.sqrt (B s) := Finset.sum_le_sum fun s _ => hpoint s
    _ ≤ Real.sqrt (∑ s, w s * B s) := hsqrt
    _ ≤ _ := Real.sqrt_le_sqrt hkey

end Corollary

end Cslib.Probability.PMF
