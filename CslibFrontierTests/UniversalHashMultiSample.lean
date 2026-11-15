/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Probability.UniversalHash.MultiSample
import CslibFrontier.Probability.StatisticalDistance.Event
import CslibFrontier.Probability.HashFamily.Polynomial
import CslibFrontier.Probability.PMF.ToReal
import Mathlib.Algebra.Field.ZMod

/-!
# Leftover hash lemma for several independent samples: hypothesis probes and instances

Checked instances and counterexamples for `CslibFrontier/Probability/UniversalHash/MultiSample.lean`
([BonehShoup2023], §8.10.4, Theorem 8.11, p. 334):

* Probe 1 (`0 ≤ 1 + α`): for the injective family `xorHash` on `Bool`, Theorem 8.11 holds with
  equality at the boundary `α = -1` (`dist = 1 / 2` for a point-mass source), while at `α = -2`
  `ENNReal.ofReal ((1 + α) / 2) = 0` clamps the negative collision bound to `0` and the formula
  evaluates to `0 < 1 / 2`.
* Probe 2 (mutual independence of samples): two independent uniform bits hashed with `xorHash`
  produce an exactly uniform tuple (`dist = 0`), whereas the correlated diagonal pair `(b, b)` with
  uniform marginals has distance `1 / 2`.
* Probe 3 (independence of seed and samples): when the sample equals the uniform seed `k`,
  `xorHash k k = false` is constant and has distance `1 / 2` from uniform.
* Probe 4 (universality of `hash`): a constant hash fails `IsTwoUniversal` and has distance `1 / 2`
  on a uniform 2-bit input, exceeding the two-universal bound `√(2 * (1 / 4)) / 2`.
* Probe 5 (guessing-probability bound `hmass`): a point-mass input under the two-universal family
  `coordHash` has distance `1 / 2`, exceeding the bound `1 / 4` at `γ = 1 / 8`.
* Concrete positive instances: a `(1 + 1) / 5`-universal polynomial hash (`α = 1 > 0`) on `Fin 3`
  over `ZMod 5`, non-identically distributed independent samples under `coordHash`, and uniform
  2-bit samples on `Fin 3`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.UniversalHashMultiSample

open Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators ENNReal

def xorHash (seed value : Bool) : Bool := value ^^ seed

theorem isUniversalHash_xorHash_zero (seed : PMF Bool) :
    IsUniversalHash seed xorHash 0 := by
  intro x y hxy
  have hempty : {s | xorHash s x = xorHash s y} = ∅ := by
    ext s
    cases x <;> cases y <;> cases s <;> simp_all [xorHash]
  simp [hempty]

def coordHash (key : Bool) (input : Bool × Bool) : Bool :=
  if key then input.1 else input.2

theorem coord_twoUniversal :
    IsTwoUniversal (PMF.uniformOfFintype Bool) coordHash :=
  isTwoUniversal_iff_sum_ite_le.mpr <| by
    rintro ⟨a, b⟩ ⟨c, d⟩ hne
    cases a <;> cases b <;> cases c <;> cases d <;>
      norm_num [coordHash, Fintype.sum_bool, PMF.uniformOfFintype_apply] at *

theorem pi_pure_unit {α : Type*} [Finite α] (a : α) :
    PMF.pi (fun _ : Unit => PMF.pure a) = PMF.pure (fun _ : Unit => a) := by
  ext f
  rw [PMF.pi_apply, Fintype.prod_unique, PMF.pure_apply, PMF.pure_apply]
  congr 1
  exact propext ⟨fun h => funext fun _ => h, fun h => congrFun h ()⟩

theorem dist_pure_uniformOfFintype_unit_bool (b : Bool) :
    dist (PMF.pure (fun _ : Unit => b)) (PMF.uniformOfFintype (Unit → Bool)) = 1 / 2 := by
  let e := Equiv.funUnique Unit Bool
  rw [← dist_map_of_injective _ _ e.injective, uniformOfFintype_map_equiv e,
    PMF.pure_map, dist_uniformOfFintype_bool]
  cases b <;> norm_num [e]

theorem dist_bind_pure_uniformOfFintype_unit_bool (f : Bool → Bool) :
    dist ((PMF.uniformOfFintype Bool).bind fun k => PMF.pure (k, fun _ : Unit => f k))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) = 1 / 2 := by
  have h1 :
      ((PMF.uniformOfFintype Bool).bind fun k => PMF.pure (k, fun _ : Unit => f k)) =
        (PMF.uniformOfFintype Bool).bind fun k =>
          (PMF.pure (fun _ : Unit => f k)).map (k, ·) := by
    simp
  rw [h1, ← PMF.uniformOfFintype_prod, dist_bind_pair]
  simp [dist_pure_uniformOfFintype_unit_bool, PMF.uniformOfFintype_apply]

/-! ### Probe 1: `0 ≤ 1 + α` is needed (and tight at `α = -1`) -/

/-- With one deterministic sample (`γ = 1`) and `xorHash`, the distance to uniform on
`Bool × (Unit → Bool)` is `1 / 2`. -/
theorem dist_seededHash_pi_xorHash_pure_unit :
    dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pi (fun _ : Unit => PMF.pure false))
        (fun s x i => xorHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) = 1 / 2 := by
  rw [pi_pure_unit]
  simpa [seededHash] using dist_bind_pure_uniformOfFintype_unit_bool (fun s => xorHash s false)

/-- At the boundary `α = -1` (`0 ≤ 1 + α` holds), `xorHash` is `(1 + (-1)) / 2 = 0`-universal, and
Theorem 8.11 gives the exact bound `1 / 2`. -/
example :
    dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pi (fun _ : Unit => PMF.pure false))
        (fun s x i => xorHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) ≤
      Fintype.card Unit * Real.sqrt (Fintype.card Bool * 1 + (-1)) / 2 := by
  have hhash : IsUniversalHash (PMF.uniformOfFintype Bool) xorHash
      (ENNReal.ofReal ((1 + (-1 : ℝ)) / Fintype.card Bool)) := by
    simpa using isUniversalHash_xorHash_zero (PMF.uniformOfFintype Bool)
  exact hhash.dist_seededHash_pi_uniformOfFintype_le (by norm_num)
    (fun _ : Unit => PMF.pure false) (fun _ x => toReal_apply_le_one (PMF.pure false) x)

/-- Without `0 ≤ 1 + α` (taking `α = -2`), `ENNReal.ofReal ((1 + α) / 2) = 0` clamps the negative
bound to `0`, so `IsUniversalHash` still holds for `xorHash`, while the Theorem 8.11 bound
evaluates to `0` and fails against the actual distance `1 / 2`. -/
theorem isUniversalHash_xorHash_neg_two :
    IsUniversalHash (PMF.uniformOfFintype Bool) xorHash
      (ENNReal.ofReal ((1 + (-2 : ℝ)) / Fintype.card Bool)) := by
  have h0 : ENNReal.ofReal ((1 + (-2 : ℝ)) / Fintype.card Bool) = 0 :=
    ENNReal.ofReal_eq_zero.mpr (by norm_num)
  rw [h0]
  exact isUniversalHash_xorHash_zero (PMF.uniformOfFintype Bool)

theorem not_dist_le_of_alpha_neg_two :
    ¬ (dist (seededHash (PMF.uniformOfFintype Bool) (PMF.pi (fun _ : Unit => PMF.pure false))
          (fun s x i => xorHash s (x i)))
        (PMF.uniformOfFintype (Bool × (Unit → Bool))) ≤
        Fintype.card Unit * Real.sqrt (Fintype.card Bool * 1 + (-2)) / 2) := by
  rw [dist_seededHash_pi_xorHash_pure_unit]
  norm_num

/-! ### Probe 2: Mutual independence of `s_1, ..., s_m` is needed -/

/-- For two independent uniform bits (`γ = 1 / 2`) hashed with `xorHash` (`α = -1`), the joint
output is exactly uniform (`dist = 0`). -/
example :
    dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Bool => PMF.uniformOfFintype Bool))
        (fun s x i => xorHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Bool → Bool))) = 0 := by
  apply le_antisymm _ dist_nonneg
  have hhash : IsUniversalHash (PMF.uniformOfFintype Bool) xorHash
      (ENNReal.ofReal ((1 + (-1 : ℝ)) / Fintype.card Bool)) := by
    simpa using isUniversalHash_xorHash_zero (PMF.uniformOfFintype Bool)
  have h := hhash.dist_seededHash_pi_uniformOfFintype_le (γ := 1 / 2) (by norm_num)
    (fun _ : Bool => PMF.uniformOfFintype Bool) (fun _ x => by
      norm_num [PMF.uniformOfFintype_apply])
  simpa using h

/-- Correlated pair `(b, b)` of uniform bits: each marginal has guessing probability `1 / 2`,
and the seed is independent, but the two digests are always equal and have distance `1 / 2` from
uniform on `Bool × (Bool → Bool)`. -/
noncomputable def diagSource : PMF (Bool → Bool) :=
  (PMF.uniformOfFintype Bool).map (fun b _ => b)

theorem diagSource_marginal (i : Bool) :
    diagSource.map (fun x => x i) = PMF.uniformOfFintype Bool := by
  rw [diagSource, PMF.map_comp]
  exact PMF.map_id _

theorem dist_seededHash_diagSource_xorHash :
    dist (seededHash (PMF.uniformOfFintype Bool) diagSource (fun s x i => xorHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Bool → Bool))) = 1 / 2 := by
  have h1 :
      seededHash (PMF.uniformOfFintype Bool) diagSource (fun s x i => xorHash s (x i)) =
        (PMF.uniformOfFintype Bool).bind fun s =>
          (diagSource.map (fun x i => xorHash s (x i))).map (s, ·) := by
    simp [seededHash, PMF.map_comp, Function.comp_def]
  have hstep (s : Bool) :
      dist (diagSource.map (fun x i => xorHash s (x i)))
        (PMF.uniformOfFintype (Bool → Bool)) = 1 / 2 := by
    let e := Equiv.boolArrowEquivProd Bool
    rw [← dist_map_of_injective _ _ e.injective, uniformOfFintype_map_equiv e,
      diagSource, PMF.map_comp, PMF.map_comp]
    cases s <;>
      norm_num [e, Equiv.boolArrowEquivProd, dist_eq, PMF.map_apply,
        PMF.uniformOfFintype_apply, tsum_fintype, Fintype.sum_prod_type, Fintype.sum_bool,
        xorHash, Function.comp_def]
  rw [h1, ← PMF.uniformOfFintype_prod, dist_bind_pair]
  simp [hstep, PMF.uniformOfFintype_apply]

/-! ### Probe 3: Independence of the seed `k` and the sample `s_1` is needed -/

/-- When the sample `s_1` equals the uniform seed `k` (so its marginal is uniform with
`γ = 1 / 2`), `xorHash k k = false` is constant and the distance to uniform is `1 / 2 > 0`. -/
theorem dist_correlatedSeed_xorHash :
    dist ((PMF.uniformOfFintype Bool).map (fun k => (k, fun _ : Unit => xorHash k k)))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) = 1 / 2 := by
  simpa [PMF.map, Function.comp_def, xorHash] using
    dist_bind_pure_uniformOfFintype_unit_bool (fun _ => false)

/-! ### Probe 4: Universality of `hash` is needed -/

def constHash (_ : Bool) (_ : Bool × Bool) : Bool := false

theorem not_isTwoUniversal_constHash :
    ¬ IsTwoUniversal (PMF.uniformOfFintype Bool) constHash := by
  rw [isTwoUniversal_iff_sum_ite_le]
  push Not
  refine ⟨(false, false), (true, false), by decide, ?_⟩
  norm_num [constHash, Fintype.sum_bool, PMF.uniformOfFintype_apply]

theorem dist_seededHash_pi_constHash :
    dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Unit => PMF.uniformOfFintype (Bool × Bool)))
        (fun s x i => constHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) = 1 / 2 := by
  have hlaw :
      seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Unit => PMF.uniformOfFintype (Bool × Bool)))
        (fun s x i => constHash s (x i)) =
      (PMF.uniformOfFintype Bool).bind fun k => PMF.pure (k, fun _ : Unit => false) := by
    simp [seededHash, constHash, PMF.map, Function.comp_def, PMF.bind_const]
  rw [hlaw]
  exact dist_bind_pure_uniformOfFintype_unit_bool (fun _ => false)

theorem not_bound_constHash :
    ¬ (dist (seededHash (PMF.uniformOfFintype Bool)
          (PMF.pi (fun _ : Unit => PMF.uniformOfFintype (Bool × Bool)))
          (fun s x i => constHash s (x i)))
        (PMF.uniformOfFintype (Bool × (Unit → Bool))) ≤
        Fintype.card Unit * Real.sqrt (Fintype.card Bool * (1 / 4 : ℝ) + 0) / 2) := by
  rw [dist_seededHash_pi_constHash]
  intro h
  have h1 : (1 : ℝ) ≤ Real.sqrt (1 / 2) := by
    simp only [Fintype.card_unique, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat, one_mul,
      add_zero] at h
    linarith
  have hsq := mul_self_le_mul_self (by norm_num) h1
  rw [Real.mul_self_sqrt (by norm_num)] at hsq
  linarith

/-! ### Probe 5: Guessing-probability bound `hmass` is needed -/

theorem dist_seededHash_pi_coordHash_pure :
    dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Unit => PMF.pure (false, false)))
        (fun s x i => coordHash s (x i)))
      (PMF.uniformOfFintype (Bool × (Unit → Bool))) = 1 / 2 := by
  rw [pi_pure_unit]
  simpa [seededHash, coordHash] using
    dist_bind_pure_uniformOfFintype_unit_bool (fun _ => false)

theorem not_dist_le_of_not_mass_le :
    ¬ (dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Unit => PMF.pure (false, false)))
        (fun s x i => coordHash s (x i)))
      ((PMF.uniformOfFintype Bool).bind
        (fun s => (PMF.uniformOfFintype (Unit → Bool)).map (s, ·))) ≤
      Fintype.card Unit * Real.sqrt (Fintype.card Bool * (1 / 8 : ℝ)) / 2) := by
  rw [PMF.uniformOfFintype_prod, dist_seededHash_pi_coordHash_pure]
  have hsqrt : Real.sqrt (2 * (1 / 8 : ℝ)) = 1 / 2 := by
    have h : (2 : ℝ) * (1 / 8 : ℝ) = (1 / 2 : ℝ) ^ 2 := by norm_num
    rw [h, Real.sqrt_sq (by norm_num)]
  simp only [Fintype.card_unit, Fintype.card_bool, Nat.cast_one, Nat.cast_ofNat, one_mul, hsqrt]
  norm_num

/-! ### Concrete positive instances -/

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Instance 1: `α = 1 > 0` (`(1 + 1) / 5`-universal two-block polynomial hash over `ZMod 5`),
-- hashing `m = 3` independent samples.
example (source : Fin 3 → PMF (ZMod 5 × ZMod 5))
    (hmass : ∀ i x, (source i x).toReal ≤ 1 / 25) :
    dist (seededHash (PMF.uniformOfFintype (ZMod 5)) (PMF.pi source)
        (fun k x i => polyHash k [(x i).1, (x i).2]))
      (PMF.uniformOfFintype (ZMod 5 × (Fin 3 → ZMod 5))) ≤
      3 * Real.sqrt (5 * (1 / 25 : ℝ) + 1) / 2 := by
  have hpoly : IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
      (fun k (p : ZMod 5 × ZMod 5) => polyHash k [p.1, p.2])
      (ENNReal.ofReal ((1 + (1 : ℝ)) / Fintype.card (ZMod 5))) := by
    have h2 : IsUniversalHash (PMF.uniformOfFintype (ZMod 5))
        (fun k (m : {m : List (ZMod 5) // m.length ≤ 2}) => polyHash k m) (2 / 5) := by
      simpa using isUniversalHash_polyHash (F := ZMod 5) 2
    have hpre := h2.precompose (encode := fun p : ZMod 5 × ZMod 5 => ⟨[p.1, p.2], by simp⟩)
      (fun p q h => by
        have h' := congrArg Subtype.val h
        simp only [List.cons.injEq, and_true] at h'
        exact Prod.ext h'.1 h'.2)
    have heq : ENNReal.ofReal ((1 + (1 : ℝ)) / Fintype.card (ZMod 5)) = (2 / 5 : ℝ≥0∞) := by
      rw [ZMod.card 5]
      norm_num [ENNReal.ofReal_div_of_pos]
    rwa [heq]
  simpa [ZMod.card 5] using
    hpoly.dist_seededHash_pi_uniformOfFintype_le (by norm_num) source hmass

-- Instance 2: Two-universal family (`α = 0`) with non-identically distributed independent samples.
example :
    dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun b : Bool =>
          if b then PMF.uniformOfFintype (Bool × Bool)
          else (PMF.uniformOfFintype Bool).map (false, ·)))
        (fun s x i => coordHash s (x i)))
      ((PMF.uniformOfFintype Bool).bind
        (fun s => (PMF.uniformOfFintype (Bool → Bool)).map (s, ·))) ≤
      Real.sqrt (2 * (1 / 4 : ℝ)) / 2 + Real.sqrt (2 * (1 / 2 : ℝ)) / 2 := by
  have h := coord_twoUniversal.leftover_hash_pi (fun b : Bool =>
    if b then PMF.uniformOfFintype (Bool × Bool)
    else (PMF.uniformOfFintype Bool).map (false, ·))
  have hcp_false : collisionProbability
      ((PMF.uniformOfFintype Bool).map (fun b => (false, b))) = 1 / 2 := by
    rw [collisionProbability_map_of_injective _ _ (fun _ _ h => (Prod.mk.injEq _ _ _ _).mp h |>.2),
      collisionProbability_uniform]
    norm_num
  simpa [Fintype.sum_bool, collisionProbability_uniform, hcp_false] using h

-- Instance 3: `IsTwoUniversal.leftover_hash_pi_of_mass_le` on `Fin 3` with `coordHash`.
example :
    dist (seededHash (PMF.uniformOfFintype Bool)
        (PMF.pi (fun _ : Fin 3 => PMF.uniformOfFintype (Bool × Bool)))
        (fun s x i => coordHash s (x i)))
      ((PMF.uniformOfFintype Bool).bind
        (fun s => (PMF.uniformOfFintype (Fin 3 → Bool)).map (s, ·))) ≤
      3 * Real.sqrt (2 * (1 / 4 : ℝ)) / 2 := by
  simpa using coord_twoUniversal.leftover_hash_pi_of_mass_le
    (fun _ : Fin 3 => PMF.uniformOfFintype (Bool × Bool))
    (γ := 1 / 4) (fun _ x => by norm_num [PMF.uniformOfFintype_apply])

end CslibFrontierTests.UniversalHashMultiSample
