/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF.Uniform

/-!
# Resampling a uniform function along a map

Draw `f : ι → κ` uniformly and, independently, a table `t : ι' → κ` uniformly. For any map
`e : ι' → ι`, the function `Function.extend e t f` is again uniform
(`uniformOfFintype_bind_bind_extend`). For injective `e` it takes the value `t j` at `e j` and
agrees with `f` off the range of `e`, so overwriting the values of a uniform function on the range
of a map by fresh uniform values leaves it uniform. This is the step that replaces part of a random
function or random oracle by an independent table.

For injective `e`, the pair `(f, t) ↦ (Function.extend e t f, f ∘ e)` is an involution, and
resampling along an equivalence (`uniformOfFintype_bind_bind_fst_equiv`) applies. A general map
is reduced to the inclusion of its range, pulling the table back along a section
(`uniformOfFintype_pi_map_comp_embedding`).

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_bind_bind_extend`: a uniform function whose values on
  the range of a map are replaced by entries of an independent uniform table is uniform.
-/

public section

namespace Cslib.Probability.PMF

variable {ι ι' κ ε : Type*}

/-- Extending by an injective `e` and then restoring the old values on the range of `e` gives back
the original function. -/
private theorem extend_comp_extend {e : ι' → ι} (he : Function.Injective e) (f : ι → κ)
    (t : ι' → κ) : Function.extend e (f ∘ e) (Function.extend e t f) = f := by
  funext i
  by_cases h : ∃ j, e j = i
  · obtain ⟨j, rfl⟩ := h
    rw [he.extend_apply]
    rfl
  · rw [Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]

/-- The injective case: `(f, t) ↦ (Function.extend e t f, f ∘ e)` is an involution. -/
private theorem uniformOfFintype_bind_bind_extend_of_injective [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] [Fintype κ] [Nonempty κ] {e : ι' → ι}
    (he : Function.Injective e) (g : (ι → κ) → PMF ε) :
    ((uniformOfFintype (ι → κ)).bind fun f =>
      (uniformOfFintype (ι' → κ)).bind fun t => g (Function.extend e t f)) =
      (uniformOfFintype (ι → κ)).bind g := by
  let swap : (ι → κ) × (ι' → κ) → (ι → κ) × (ι' → κ) := fun p =>
    (Function.extend e p.2 p.1, p.1 ∘ e)
  have hswap : Function.Involutive swap := fun p =>
    Prod.ext (extend_comp_extend he p.1 p.2) (Function.extend_comp he p.2 p.1)
  exact uniformOfFintype_bind_bind_fst_equiv hswap.toPerm g

/-- **Resampling along a map**: a uniform function whose values on the range of `e` are replaced
by entries of an independent uniform table is uniform. For injective `e`, the function
`Function.extend e t f` takes the value `t j` at `e j` and the value of `f` off the range of `e`. -/
theorem uniformOfFintype_bind_bind_extend [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] [Fintype κ] [Nonempty κ] (e : ι' → ι) (g : (ι → κ) → PMF ε) :
    ((uniformOfFintype (ι → κ)).bind fun f =>
      (uniformOfFintype (ι' → κ)).bind fun t => g (Function.extend e t f)) =
      (uniformOfFintype (ι → κ)).bind g := by
  classical
  let σ : {i // ∃ j, e j = i} → ι' := fun i => i.2.choose
  have hσ : Function.Injective σ := fun a b h =>
    Subtype.ext (by rw [← a.2.choose_spec, ← b.2.choose_spec]; exact congrArg e h)
  have hext (t : ι' → κ) (f : ι → κ) :
      Function.extend e t f = Function.extend Subtype.val (t ∘ σ) f := by
    funext i
    by_cases h : ∃ j, e j = i
    · rw [Function.extend_def, dite_eq_left h]
      exact (Subtype.val_injective.extend_apply (t ∘ σ) f ⟨i, h⟩).symm
    · rw [Function.extend_apply' _ _ _ h,
        Function.extend_apply' _ _ _ (by rintro ⟨⟨i', hi'⟩, rfl⟩; exact h hi')]
  have hpull (f : ι → κ) :
      ((uniformOfFintype (ι' → κ)).bind fun t => g (Function.extend Subtype.val (t ∘ σ) f)) =
        (uniformOfFintype ({i // ∃ j, e j = i} → κ)).bind fun t' =>
          g (Function.extend Subtype.val t' f) := by
    rw [← uniformOfFintype_pi_map_comp_embedding ⟨σ, hσ⟩, PMF.bind_map]
    rfl
  simp only [hext, hpull]
  exact uniformOfFintype_bind_bind_extend_of_injective Subtype.val_injective g

end Cslib.Probability.PMF
