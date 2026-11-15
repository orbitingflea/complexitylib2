/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.List.Binary
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# Bounded binary enumeration

Fixed-width words enumerate each natural number below their range exactly once. The weighted
sum identity generalizes the corresponding counting argument, and applies to both natural and
signed summands. Values outside a requested interval contribute zero.

## Main results

* `Cslib.BitString.sum_binaryValue_lt`: a bounded natural sum as a sum over fixed-width words.
-/

public section

namespace Cslib.BitString

/-- Fixed-width binary enumeration preserves a sum on an initial interval of its range. -/
theorem sum_binaryValue_lt {M : Type*} [AddCommMonoid M] {n k : ℕ} (hk : k ≤ 2 ^ n)
    (f : ℕ → M) :
    (∑ w : Fin n → Bool,
      if binaryValue (List.ofFn w) < k then f (binaryValue (List.ofFn w)) else 0) =
        ∑ i ∈ Finset.range k, f i := by
  classical
  rw [← Finset.sum_filter]
  apply Finset.sum_bij (fun w _ => binaryValue (List.ofFn w))
  · intro w hw
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range] using hw
  · intro u _ v _ h
    exact List.ofFn_injective (binaryValue_injective_of_length_eq (by simp) h)
  · intro j hj
    obtain ⟨w, hw⟩ := exists_binaryValue_eq ((Finset.mem_range.mp hj).trans_le hk)
    exact ⟨w, by simpa [hw] using hj, hw⟩
  · intro _ _
    rfl

end Cslib.BitString
