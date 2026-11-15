/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Enumerating a prime field by natural representatives

The enumeration bridge needs only a nonzero modulus. `Fintype.sum_extend_by_zero` supplies
restriction to a finite subset.

These identities separate finite-field enumeration from the bit-cost certificates of its
computational realizations.
-/

public section

namespace ZMod

/-- Summing over least natural representatives enumerates a nonzero residue ring once. -/
theorem sum_range_natCast {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (h : ZMod n → M) :
    (∑ g ∈ Finset.range n, h (g : ZMod n)) = ∑ γ : ZMod n, h γ := by
  classical
  exact Finset.sum_nbij' (fun g : ℕ => (g : ZMod n)) ZMod.val
    (fun _ _ => Finset.mem_univ _)
    (fun γ _ => Finset.mem_range.mpr γ.val_lt)
    (fun g hg => ZMod.val_natCast_of_lt (Finset.mem_range.mp hg))
    (fun γ _ => ZMod.natCast_zmod_val γ)
    (fun _ _ => rfl)

/-- Restricting the enumeration by membership gives a sum over the chosen finite subset. -/
theorem sum_range_natCast_mem {n : ℕ} [NeZero n] {M : Type*} [AddCommMonoid M]
    (s : Finset (ZMod n)) (h : ZMod n → M) :
    (∑ g ∈ Finset.range n, if (g : ZMod n) ∈ s then h (g : ZMod n) else 0) =
      ∑ γ ∈ s, h γ := by
  classical
  rw [sum_range_natCast (fun x => if x ∈ s then h x else 0)]
  exact Fintype.sum_extend_by_zero s h

/-- Natural representative tests count a finite subset exactly. In particular this applies to
`primitiveRoots (p - 1) (ZMod p)`, with cardinality bounds supplied by GeneratorProducts. -/
theorem count_range_natCast_mem {n : ℕ} [NeZero n] (s : Finset (ZMod n)) :
    (∑ g ∈ Finset.range n, if (g : ZMod n) ∈ s then 1 else 0) = s.card := by
  classical
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using
    sum_range_natCast_mem (M := ℕ) s (fun _ => 1)


end ZMod
