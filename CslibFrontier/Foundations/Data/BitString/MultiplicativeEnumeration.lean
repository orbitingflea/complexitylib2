/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.WeightedEnumeration

/-!
# Multiplicative binary enumeration

Products over fixed-width words enumerate a bounded interval or a finite subset once.
The interval result is the additive enumeration theorem transported through `Additive`.

## Main results

* `Cslib.BitString.prod_binaryValue_lt`: multiplicative bounded enumeration.
* `Cslib.BitString.prod_binaryValue_mem`: multiplicative finite-subset enumeration.
-/

public section

namespace Cslib.BitString

open Finset

/-- Fixed-width binary enumeration preserves a product on an initial interval. -/
theorem prod_binaryValue_lt {M : Type*} [CommMonoid M] {n k : ℕ} (hk : k ≤ 2 ^ n)
    (f : ℕ → M) :
    (∏ w : Fin n → Bool,
      if binaryValue (List.ofFn w) < k then f (binaryValue (List.ofFn w)) else 1) =
        ∏ i ∈ range k, f i := by
  have h := sum_binaryValue_lt (M := Additive M) hk (fun i => Additive.ofMul (f i))
  simpa only [toMul_sum, apply_ite, toMul_ofMul, toMul_zero] using
    congrArg Additive.toMul h

/-- A finite subset below the binary width is enumerated once, with unit factors elsewhere. -/
theorem prod_binaryValue_mem {M : Type*} [CommMonoid M] {n k : ℕ}
    (hk : k ≤ 2 ^ n) (s : Finset ℕ) (hs : s ⊆ range k) (f : ℕ → M) :
    (∏ w : Fin n → Bool,
      if binaryValue (List.ofFn w) ∈ s then f (binaryValue (List.ofFn w)) else 1) =
        ∏ i ∈ s, f i := by
  calc
    _ = ∏ w : Fin n → Bool, if binaryValue (List.ofFn w) < k then
        (if binaryValue (List.ofFn w) ∈ s then f (binaryValue (List.ofFn w)) else 1)
        else 1 := by
      apply prod_congr rfl
      intro w _
      by_cases hw : binaryValue (List.ofFn w) ∈ s
      · simp [hw, mem_range.mp (hs hw)]
      · simp [hw]
    _ = ∏ i ∈ range k, if i ∈ s then f i else 1 :=
      prod_binaryValue_lt hk (fun i => if i ∈ s then f i else 1)
    _ = ∏ i ∈ s, f i := by
      rw [← prod_filter]
      congr 1
      ext i
      simp only [mem_filter, mem_range]
      exact ⟨And.right, fun hi => ⟨mem_range.mp (hs hi), hi⟩⟩

end Cslib.BitString
