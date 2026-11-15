/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Game.Inversion
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Probability.Guessing.Leakage
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Second-preimage experiments and finite bounds

The second-preimage experiment for a function and an input distribution, with the finite-domain
counting and inversion bounds of [BonehShoup2023], Exercise 8.23(a)–(b), pp. 352–353. Below,
`OWadv[A, H]` and `SPRadv[B, H]` are the success probabilities of `inversionExperiment` and
`secondPreimageExperiment`, and `B := fun m => A (H m)` is the finder that runs the inverter `A`
on the digest.

The asymptotic bit-string notion `SecondPreimageResistant` lives in
`CslibFrontier.Crypto.Computational.SecondPreimageResistant`.

## Main definitions

* `Cslib.Crypto.secondPreimageExperiment`: draw `x ← sample`, run `x' ← finder x`, and accept when
  `x' ≠ x` and `f x' = f x`.
* `Cslib.Crypto.HasSecondPreimage`: `∃ m' ≠ m, H m' = H m`.

## Main results

* `Cslib.Crypto.card_not_hasSecondPreimage_le`,
  `Cslib.Crypto.card_not_hasSecondPreimage_div_le`: at most `|T|` inputs lack a second preimage,
  which is at most a `1 / s` fraction when `s * |T| ≤ |M|` and `0 < s` (Exercise 8.23(a)).
* `Cslib.Crypto.inversionExperiment_le_secondPreimageExperiment_add`: for any input distribution
  `sample`, `OWadv[A, H] ≤ SPRadv[B, H] + ∑' x, sample x * A (H x) x`.
* `Cslib.Crypto.succProbability_inversionExperiment_uniform_le_add_card_div`: on a uniform input
  from a nonempty finite `M`, `OWadv[A, H] ≤ SPRadv[B, H] + |T| / |M|`.
* `Cslib.Crypto.succProbability_inversionExperiment_uniform_le_two_mul_add_div`: equation (8.22)
  of Exercise 8.23(b), `OWadv[A, H] ≤ 2 · SPRadv[B, H] + 1 / s` when `s * |T| ≤ |M|` and `0 < s`.
  It follows from the previous bound, which shows that the factor `2` is not needed.
* `Cslib.Crypto.succProbability_secondPreimageExperiment_le_of_eq_imp`: a finder succeeds against
  `g` at most as often as against `f` when every collision of `g` on distinct inputs is one of `f`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 8.11.1 (Definition 8.6, p. 336) and Exercise 8.23(a)–(b) (pp. 352–353).
-/

public section

open Cslib.Probability Cslib.Probability.PMF
open scoped NNReal ENNReal

namespace Cslib.Crypto

variable {m : Type → Type*} [Monad m] {α : Type} {β : Type*}

/-- The second-preimage experiment for `f` on inputs drawn from `sample`: the challenger draws `x`
and gives `finder` the input `x`; `finder` wins when it returns `x' ≠ x` with `f x' = f x`. -/
@[expose]
def secondPreimageExperiment [BEq α] [BEq β] (sample : m α) (f : α → β) (finder : α → m α) :
    m Bool := do
  let x ← sample
  let x' ← finder x
  return x' != x && f x' == f x

/-- On distributions, the second-preimage experiment maps the finder's output distribution through
the distinctness and collision test. -/
theorem secondPreimageExperiment_eq_bind_map [BEq α] [BEq β] (sample : PMF α) (f : α → β)
    (finder : α → PMF α) :
    secondPreimageExperiment sample f finder =
      sample.bind fun x => (finder x).map fun x' => x' != x && f x' == f x :=
  rfl

/-- An injective function has no second preimages, so every second-preimage finder fails with
probability `1`. -/
theorem secondPreimageExperiment_eq_pure_false_of_injective [BEq α] [LawfulBEq α]
    [BEq β] [LawfulBEq β] (sample : PMF α) {f : α → β} (hf : Function.Injective f)
    (finder : α → PMF α) :
    secondPreimageExperiment sample f finder = PMF.pure false := by
  have heq (x' x : α) : (x' != x && f x' == f x) = false := by
    by_cases h : x' = x
    · simp [h]
    · have hne : f x' ≠ f x := fun hfx => h (hf hfx)
      simp [h, hne]
  simp only [secondPreimageExperiment, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, heq,
    PMF.bind_const]

/-- If every collision under `g` is a collision under `f`, then every second-preimage finder
succeeds at least as often against `f` as against `g`. -/
theorem succProbability_secondPreimageExperiment_le_of_eq_imp {α : Type} {β γ : Type*}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] [BEq γ] [LawfulBEq γ]
    (sample : PMF α) {f : α → β} {g : α → γ}
    (himp : ∀ x x', x' ≠ x → g x' = g x → f x' = f x) (finder : α → PMF α) :
    Game.succProbability (secondPreimageExperiment sample g finder) ≤
      Game.succProbability (secondPreimageExperiment sample f finder) := by
  apply Game.succProbability_mono
  simp only [secondPreimageExperiment_eq_bind_map]
  refine PMF.bind_apply_mono_on_support _ _ fun x _ =>
    PMF.map_true_mono _ fun x' _ h => ?_
  rw [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at h ⊢
  exact ⟨h.1, himp x x' h.1 h.2⟩

/-! ## Finite-domain counting and (8.22) (Exercise 8.23(a)–(b)) -/

/-- `m` has a second preimage under `H` when some distinct `m' ≠ m` maps to the same digest. -/
@[expose]
def HasSecondPreimage {M T : Type*} (H : M → T) (m : M) : Prop :=
  ∃ m' : M, m' ≠ m ∧ H m' = H m

instance {M T : Type*} [Fintype M] [DecidableEq M] [DecidableEq T] (H : M → T) :
    DecidablePred (HasSecondPreimage H) :=
  fun _ => Fintype.decidableExistsFintype

/-- An input lacking a second preimage is uniquely determined by its digest. -/
theorem eq_of_apply_eq_of_not_hasSecondPreimage {M T : Type*} {H : M → T} {m₁ m₂ : M}
    (hm₁ : ¬ HasSecondPreimage H m₁) (heq : H m₁ = H m₂) : m₁ = m₂ := by
  by_contra hne
  exact hm₁ ⟨m₂, Ne.symm hne, heq.symm⟩

/-- **Exercise 8.23(a), count form** ([BonehShoup2023], p. 352): at most `|T|` inputs in `M` lack
a second preimage under `H : M → T`. -/
theorem card_not_hasSecondPreimage_le {M T : Type*} [Fintype M] [Fintype T] (H : M → T)
    [DecidablePred fun m : M => ¬ HasSecondPreimage H m] :
    (Finset.univ.filter fun m : M => ¬ HasSecondPreimage H m).card ≤ Fintype.card T :=
  Finset.card_le_card_of_injOn H (fun _ _ => Finset.mem_univ _) fun _ hm₁ _ _ h =>
    eq_of_apply_eq_of_not_hasSecondPreimage (Finset.mem_filter.mp hm₁).2 h

/-- **Exercise 8.23(a), fraction form** ([BonehShoup2023], p. 352): if `|M| ≥ s · |T|` with
`0 < s` (the book assumes `s > 1`, and `0 < s` suffices), then at most a `1 / s` fraction of
inputs in `M` lack a second preimage. -/
theorem card_not_hasSecondPreimage_div_le {M T : Type*} [Fintype M] [Fintype T]
    (H : M → T) [DecidablePred fun m : M => ¬ HasSecondPreimage H m]
    {s : ℝ} (hs : 0 < s) (hM : s * Fintype.card T ≤ Fintype.card M) :
    ((Finset.univ.filter fun m : M => ¬ HasSecondPreimage H m).card : ℝ) / Fintype.card M ≤
      1 / s := by
  have hcard : ((Finset.univ.filter fun m : M => ¬ HasSecondPreimage H m).card : ℝ) ≤
      Fintype.card T := by
    exact_mod_cast card_not_hasSecondPreimage_le H
  refine div_le_of_le_mul₀ (Nat.cast_nonneg _) (by positivity) ?_
  rw [one_div, inv_mul_eq_div, le_div_iff₀ hs]
  nlinarith

/-- Distributional split behind (8.22): for any input law `sample`, an inverter `A` either finds
a second preimage when invoked as `x ↦ A (f x)` or hits the challenge `x` itself. -/
theorem inversionExperiment_le_secondPreimageExperiment_add {α : Type} {β : Type*}
    [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] (sample : PMF α) (f : α → β) (A : β → PMF α) :
    inversionExperiment sample f A true ≤
      secondPreimageExperiment sample f (fun x => A (f x)) true + ∑' x, sample x * A (f x) x := by
  rw [inversionExperiment_eq_bind_map, secondPreimageExperiment_eq_bind_map, PMF.bind_apply,
    PMF.bind_apply, ← tsum_add]
  refine tsum_le_tsum fun x => ?_
  rw [← mul_add]
  gcongr
  refine (PMF.map_true_le_add (A (f x)) (A := fun x' => x' != x && f x' == f x)
    (B := fun x' => x' == x) fun x' _ h => ?_).trans ?_
  · by_cases hx : x' = x
    · exact Or.inr (by simp [hx])
    · exact Or.inl (by simpa [hx] using h)
  · gcongr
    rw [PMF.map_apply_true, tsum_eq_single x (fun a ha => by simp [ha])]
    simp

/-- Factor-one uniform inversion bound: the second-preimage finder `B := fun m => A (H m)` built
from an inverter `A` satisfies `OWadv[A, H] ≤ SPRadv[B, H] + |T| / |M|`, without the factor `2` of
(8.22). -/
theorem succProbability_inversionExperiment_uniform_le_add_card_div
    {M : Type} {T : Type*} [Fintype M] [Nonempty M] [DecidableEq M] [Fintype T] [DecidableEq T]
    (H : M → T) (A : T → PMF M) :
    (Game.succProbability (inversionExperiment (uniformOfFintype M) H A) : ℝ) ≤
      (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) +
        (Fintype.card T : ℝ) / Fintype.card M := by
  have hcard_ne : (Fintype.card M : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have henn : inversionExperiment (uniformOfFintype M) H A true ≤
      secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m)) true +
        (Fintype.card T : ℝ≥0∞) * (Fintype.card M : ℝ≥0∞)⁻¹ := by
    refine (inversionExperiment_le_secondPreimageExperiment_add _ H A).trans (add_le_add le_rfl ?_)
    refine (PMF.tsum_mul_apply_le_card_mul (uniformOfFintype M)
      (fun x => (uniformOfFintype_apply x).le) H Finset.univ (fun _ => Finset.mem_univ _) A).trans
      ?_
    rw [Finset.card_univ]
  have hterm : (Fintype.card T : ℝ≥0∞) * (Fintype.card M : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hcard_ne)
  have hreal := (ENNReal.toReal_le_toReal (PMF.apply_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, hterm⟩)).mpr henn
  simpa only [Game.succProbability, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_add (PMF.apply_ne_top _ _) hterm, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, div_eq_mul_inv] using hreal

/-- **Exercise 8.23(b), equation (8.22)** ([BonehShoup2023], p. 353): when `|M| ≥ s · |T|` with
`0 < s`, the second-preimage finder `B := fun m => A (H m)` built from an inverter `A` satisfies
`OWadv[A, H] ≤ 2 · SPRadv[B, H] + 1 / s`. This weakens
`succProbability_inversionExperiment_uniform_le_add_card_div`, which shows that the factor `2` is
not needed. -/
theorem succProbability_inversionExperiment_uniform_le_two_mul_add_div
    {M : Type} {T : Type*} [Fintype M] [Nonempty M] [DecidableEq M] [Fintype T] [DecidableEq T]
    (H : M → T) (A : T → PMF M) {s : ℝ} (hs : 0 < s)
    (hM : s * Fintype.card T ≤ Fintype.card M) :
    (Game.succProbability (inversionExperiment (uniformOfFintype M) H A) : ℝ) ≤
      2 * (Game.succProbability
        (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) +
        1 / s := by
  have h1 := succProbability_inversionExperiment_uniform_le_add_card_div H A
  have hM' : (0 : ℝ) < Fintype.card M := Nat.cast_pos.mpr Fintype.card_pos
  have h2 : (Fintype.card T : ℝ) / Fintype.card M ≤ 1 / s := by
    rw [div_le_div_iff₀ hM' hs]
    linarith
  have h3 : (0 : ℝ) ≤ (Game.succProbability
      (secondPreimageExperiment (uniformOfFintype M) H (fun m => A (H m))) : ℝ) :=
    NNReal.coe_nonneg _
  linarith

end Cslib.Crypto

namespace Cslib.ProbComp

open Cslib.Crypto

variable {α : Type} {β : Type}

/-- Evaluating the second-preimage experiment of programs gives the second-preimage experiment of
their distributions. -/
@[simp]
theorem eval_secondPreimageExperiment [BEq α] [BEq β] (sample : ProbComp α) (f : α → β)
    (finder : α → ProbComp α) :
    eval (secondPreimageExperiment sample f finder) =
      secondPreimageExperiment (eval sample) f (fun x => eval (finder x)) := by
  simp only [secondPreimageExperiment, eval_bind, eval_pure]
  rfl

end Cslib.ProbComp
