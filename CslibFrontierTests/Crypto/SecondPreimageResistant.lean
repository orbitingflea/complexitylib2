/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.SecondPreimageResistant
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Tactic.NormNum

/-!
# Tests for second-preimage resistance

Checks for `CslibFrontier/Crypto/Game/SecondPreimage.lean` and
`CslibFrontier/Crypto/Computational/SecondPreimageResistant.lean` as a `module` client with
ordinary imports:

* Concrete evaluation of `HasSecondPreimage` on `Bool`, applying `card_not_hasSecondPreimage_le`
  and `card_not_hasSecondPreimage_div_le` (with a counterexample showing `0 < s` is needed at
  `s = 0`), and instantiating both `succProbability_inversionExperiment_uniform_le_add_card_div`
  and `succProbability_inversionExperiment_uniform_le_two_mul_add_div` (`1 = 1 / 2 + 1 / 2` on
  `H : Bool → Unit`, showing the factor-one bound is tight).
* The finite-domain construction `revealAtZero : T × Fin (2 * s) → T × Bool` (compression ratio
  `s`, since `|T × Fin (2 * s)| = s · |T × Bool|`) of [BonehShoup2023], Exercise 8.23(c), p. 353,
  checked with `succProbability_secondPreimageExperiment_le_of_eq_imp`: second-preimage
  preservation (`succProbability_secondPreimageExperiment_revealAtZero_le`) and exact inversion
  probability `1 / (2 * s)` (`1 / 4` at `s = 2`, `T = Bool`).
* Unconditional `SecondPreimageResistant id` and the nonvacuity witness
  `not_secondPreimageResistant_const_empty` for the `SecondPreimageResistant` row of
  `assumptions.md`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SecondPreimageResistant

open Cslib Cslib.Crypto Cslib.ProbComp Cslib.Probability Cslib.Probability.PMF
open Turing.MultiTapeTM
open scoped NNReal ENNReal

/-- On `Bool`, `id` has no inputs with a second preimage (`2` elements lack one, matching
`card_not_hasSecondPreimage_le` and `card_not_hasSecondPreimage_div_le` at `s = 1`). -/
theorem card_not_hasSecondPreimage_id_bool :
    (Finset.univ.filter (fun m : Bool => ¬ HasSecondPreimage id m)).card = 2 := by
  decide

example :
    ((Finset.univ.filter (fun m : Bool => ¬ HasSecondPreimage id m)).card : ℝ) /
      Fintype.card Bool ≤ 1 / (1 : ℝ) :=
  card_not_hasSecondPreimage_div_le (id : Bool → Bool) one_pos (by simp)

/-- Probe: `0 < s` is needed in `card_not_hasSecondPreimage_div_le`; at `s = 0` with `id` on
`Bool`, `0 * |Bool| ≤ |Bool|` holds while the `1 / 0` conclusion (`1 ≤ 0`) fails. -/
example :
    (0 : ℝ) * Fintype.card Bool ≤ Fintype.card Bool ∧
      ¬ ((Finset.univ.filter (fun m : Bool => ¬ HasSecondPreimage id m)).card : ℝ) /
          Fintype.card Bool ≤ 1 / (0 : ℝ) := by
  refine ⟨by simp, ?_⟩
  rw [card_not_hasSecondPreimage_id_bool, Fintype.card_bool]
  norm_num

/-- Without compression (`M = T = Bool`, `H = id`), `OWadv[pure, id] = 1` while
`SPRadv[pure ∘ id, id] = 0`: both `succProbability_inversionExperiment_uniform_le_add_card_div`
and `succProbability_inversionExperiment_uniform_le_two_mul_add_div` (at `s = 1`) apply and give
`1 ≤ 0 + 1`. -/
theorem succProbability_inversionExperiment_id_bool :
    (Game.succProbability (inversionExperiment (uniformOfFintype Bool) id PMF.pure) : ℝ) = 1 := by
  have heval : inversionExperiment (uniformOfFintype Bool) id PMF.pure = PMF.pure true := by
    simp [inversionExperiment]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one, NNReal.coe_one]

theorem succProbability_secondPreimageExperiment_id_bool :
    (Game.succProbability
      (secondPreimageExperiment (uniformOfFintype Bool) id
        (fun m => PMF.pure (id m))) : ℝ) = 0 := by
  rw [secondPreimageExperiment_eq_pure_false_of_injective _ Function.injective_id]
  simp [Game.succProbability]

example :
    (Game.succProbability (inversionExperiment (uniformOfFintype Bool) id PMF.pure) : ℝ) ≤
      (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype Bool) id
          (fun m => PMF.pure (id m))) : ℝ) +
        (Fintype.card Bool : ℝ) / Fintype.card Bool :=
  succProbability_inversionExperiment_uniform_le_add_card_div id PMF.pure

example :
    (Game.succProbability (inversionExperiment (uniformOfFintype Bool) id PMF.pure) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype Bool) id
          (fun m => PMF.pure (id m))) : ℝ) +
        1 / (1 : ℝ) :=
  succProbability_inversionExperiment_uniform_le_two_mul_add_div id PMF.pure one_pos (by simp)

/-- When `H : Bool → Unit` is constant and `A () = pure false`, `OWadv[A, H] = 1` and
`SPRadv[A ∘ H, H] = 1 / 2`: the factor-one bound
`succProbability_inversionExperiment_uniform_le_add_card_div` is an equality (`1 = 1 / 2 + 1 / 2`),
and `succProbability_inversionExperiment_uniform_le_two_mul_add_div` applies at `s = 2`. -/
theorem succProbability_inversionExperiment_const_bool :
    (Game.succProbability
      (inversionExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
        (fun _ => PMF.pure false)) : ℝ) = 1 := by
  have heval :
      inversionExperiment (uniformOfFintype Bool) (fun _ : Bool => ()) (fun _ => PMF.pure false) =
        PMF.pure true := by
    simp [inversionExperiment]
  rw [heval, Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one, NNReal.coe_one]

theorem succProbability_secondPreimageExperiment_const_bool :
    (Game.succProbability
      (secondPreimageExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
        (fun _ => PMF.pure false)) : ℝ) = 1 / 2 := by
  have heval :
      (secondPreimageExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
        (fun _ => PMF.pure false)) true =
        (uniformOfFintype Bool).toOuterMeasure {m : Bool | m = true} := by
    rw [secondPreimageExperiment_eq_bind_map, PMF.toOuterMeasure_apply]
    simp only [PMF.bind_apply, PMF.pure_map, PMF.pure_apply, Set.indicator_apply,
      Set.mem_ofPred_eq]
    congr 1 with m
    cases m <;> simp
  have hcard :
      (Finset.univ.filter (fun m : Bool => m ∈ {m : Bool | m = true})).card = 1 := by decide
  rw [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, hcard, Fintype.card_bool]
  norm_num

example :
    (Game.succProbability
      (inversionExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
        (fun _ => PMF.pure false)) : ℝ) ≤
      (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
          (fun _ => PMF.pure false)) : ℝ) +
        (Fintype.card Unit : ℝ) / Fintype.card Bool :=
  succProbability_inversionExperiment_uniform_le_add_card_div (fun _ : Bool => ())
    (fun _ => PMF.pure false)

example :
    (Game.succProbability
      (inversionExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
        (fun _ => PMF.pure false)) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype Bool) (fun _ : Bool => ())
          (fun _ => PMF.pure false)) : ℝ) +
        1 / (2 : ℝ) :=
  succProbability_inversionExperiment_uniform_le_two_mul_add_div (fun _ : Bool => ())
    (fun _ => PMF.pure false) (by norm_num) (by simp)

/-! ### Checked instance of Exercise 8.23(c) (`revealAtZero : T × Fin (2 * s) → T × Bool`) -/

/-- The finite-domain construction `H' : T × Fin (2 * s) → T × Bool` of [BonehShoup2023],
Exercise 8.23(c), p. 353 (compression ratio `s`, since `|T × Fin (2 * s)| = s · |T × Bool|`):
reveal `m.1` tagged with `true` when `m.2.val = 0`, and output `(H m, false)` otherwise. -/
def revealAtZero {T : Type*} {s : ℕ} (H : T × Fin (2 * s) → T)
    (m : T × Fin (2 * s)) : T × Bool :=
  if m.2.val == 0 then (m.1, true) else (H m, false)

/-- Every second preimage of `m` under `revealAtZero H` is a second preimage of `m` under `H`:
inputs with `m.2.val = 0` have no second preimage under `revealAtZero H`. -/
theorem eq_of_revealAtZero_eq {T : Type*} {s : ℕ}
    (H : T × Fin (2 * s) → T) {m m' : T × Fin (2 * s)} (hne : m' ≠ m)
    (heq : revealAtZero H m' = revealAtZero H m) :
    H m' = H m := by
  unfold revealAtZero at heq
  split_ifs at heq with hm' hm
  · exfalso
    apply hne
    ext
    · exact (Prod.mk.inj heq).1
    · rw [beq_iff_eq] at hm' hm
      exact hm'.trans hm.symm
  · cases (Prod.mk.inj heq).2
  · cases (Prod.mk.inj heq).2
  · exact (Prod.mk.inj heq).1

/-- **Exercise 8.23(c), second-preimage preservation** ([BonehShoup2023], p. 353): for every
second-preimage finder `B`, its success probability against `revealAtZero H` is at most its
success probability against `H`. -/
theorem succProbability_secondPreimageExperiment_revealAtZero_le
    {T : Type} [DecidableEq T] {s : ℕ} (sample : PMF (T × Fin (2 * s)))
    (H : T × Fin (2 * s) → T) (B : T × Fin (2 * s) → PMF (T × Fin (2 * s))) :
    Game.succProbability (secondPreimageExperiment sample (revealAtZero H) B) ≤
      Game.succProbability (secondPreimageExperiment sample H B) :=
  succProbability_secondPreimageExperiment_le_of_eq_imp sample
    (fun _ _ hne heq => eq_of_revealAtZero_eq H hne heq) B

/-- **Exercise 8.23(c), inversion attack** ([BonehShoup2023], p. 353): when `0 < s`, the inverter
`y ↦ (y.1, 0)` inverts `revealAtZero H` with probability `1 / (2 * s)` (`1 / 4` at `s = 2`),
whatever `H` is. -/
theorem succProbability_inversionExperiment_revealAtZero
    {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] {s : ℕ} [NeZero s]
    (H : T × Fin (2 * s) → T) :
    (Game.succProbability
      (inversionExperiment (uniformOfFintype (T × Fin (2 * s))) (revealAtZero H)
        (fun y => PMF.pure (y.1, ⟨0, Nat.mul_pos two_pos (NeZero.pos s)⟩))) : ℝ) =
      1 / (2 * s) := by
  let z : Fin (2 * s) := ⟨0, Nat.mul_pos two_pos (NeZero.pos s)⟩
  have hcheck (m : T × Fin (2 * s)) :
      (revealAtZero H ((revealAtZero H m).1, z) == revealAtZero H m) =
        decide (m.2 = z) := by
    unfold revealAtZero
    by_cases hm : m.2 = z
    · simp [hm, z]
    · have hval : (m.2.val == 0) = false :=
        beq_eq_false_iff_ne.mpr (fun h => hm (Fin.ext h))
      have hneq : ((H m, true) == (H m, false)) = false :=
        beq_eq_false_iff_ne.mpr (fun h => by cases (Prod.mk.inj h).2)
      simp only [hval, Bool.false_eq_true, ↓reduceIte, hneq, hm, decide_false, z, beq_self_eq_true]
  have heval :
      (inversionExperiment (uniformOfFintype (T × Fin (2 * s))) (revealAtZero H)
        (fun y => PMF.pure (y.1, z))) true =
        (uniformOfFintype (T × Fin (2 * s))).toOuterMeasure
          {m : T × Fin (2 * s) | m.2 = z} := by
    rw [inversionExperiment_eq_bind_map, PMF.toOuterMeasure_apply]
    simp only [PMF.bind_apply, PMF.pure_map, hcheck, PMF.pure_apply, Set.indicator_apply,
      Set.mem_ofPred_eq]
    congr 1 with m
    by_cases hm : m.2 = z <;> simp [hm]
  have hcard :
      (Finset.univ.filter (fun m : T × Fin (2 * s) => m ∈ {m : T × Fin (2 * s) | m.2 = z})).card =
        Fintype.card T := by
    have hbij :
        Finset.univ.filter (fun m : T × Fin (2 * s) => m ∈ {m : T × Fin (2 * s) | m.2 = z}) =
          (Finset.univ : Finset T).image (fun t => (t, z)) := by
      ext ⟨t, i⟩
      simp [eq_comm]
    rw [hbij, Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1), Finset.card_univ]
  have hT_ne : (Fintype.card T : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal, heval,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_toReal, hcard, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, Nat.cast_mul, Nat.cast_ofNat, ← div_div, div_self hT_ne]

/-- Exercise 8.23(c) at `s = 2` and `T = Bool`: inversion success `1 / 4`. -/
example (H : Bool × Fin 4 → Bool) :
    (Game.succProbability
      (inversionExperiment (uniformOfFintype (Bool × Fin 4)) (revealAtZero (s := 2) H)
        (fun y => PMF.pure (y.1, ⟨0, by decide⟩))) : ℝ) = 1 / 4 := by
  rw [succProbability_inversionExperiment_revealAtZero (T := Bool) (s := 2) H]
  norm_num

/-- The identity on bit strings is unconditionally `SecondPreimageResistant`. -/
theorem secondPreimageResistant_id : SecondPreimageResistant id :=
  SecondPreimageResistant.of_injective (ComputableInPolyTime.id' (encIn := encBits))
    Function.injective_id

/-- Nonvacuity test for the `SecondPreimageResistant` row of `assumptions.md`. -/
theorem not_secondPreimageResistant_const_empty : ¬ SecondPreimageResistant (fun _ => []) :=
  not_secondPreimageResistant_const []

end CslibFrontierTests.Crypto.SecondPreimageResistant
