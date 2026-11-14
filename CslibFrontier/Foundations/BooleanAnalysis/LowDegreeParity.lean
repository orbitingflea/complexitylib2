/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Degree
public import CslibFrontier.Foundations.BooleanAnalysis.LowDegreePhase

/-!
# Parity is far from low-degree functions

Over a field `F` in which `2` is invertible, a function of degree at most `D` agrees with the parity
of all `|ι|` coordinates on at most as many inputs as there are sets of at most `|ι| / 2 + D`
coordinates (`BitString.card_agree_parityOn_univ_le`) [Smolensky1987]. This is the `ω = -1` case of
`BitString.exists_agree_of_phaseChar` and `BitString.card_le_of_forall_exists_agree` in
`CslibFrontier.Foundations.BooleanAnalysis.LowDegreePhase`, since `chi F = phaseChar (-1)`.

## Main results

* `Cslib.BitString.exists_agree_of_parity`: if `Q` of degree `D` agrees with the full character on
  `G`, every function on `G` agrees with one of degree at most `|ι| / 2 + D`.
* `Cslib.BitString.card_agree_parityOn_univ_le`, `Cslib.BitString.card_agree_parity_le`: parity
  is far from low-degree functions.

## References

* [R. Smolensky, *Algebraic methods in the theory of lower bounds for Boolean circuit
  complexity*][Smolensky1987]
-/

public section

namespace Cslib.BitString

open Finset

variable {F : Type*} [Field F] {ι : Type*} [Fintype ι]

/-- If `Q` has degree at most `D` and agrees with the character of all coordinates on `G`, every
function agrees on `G` with a function of degree at most `|ι| / 2 + D`. -/
theorem exists_agree_of_parity [Invertible (2 : F)] {D : ℕ} {Q : (ι → Bool) → F}
    (hQ : Q ∈ lowDegree F ι D) (G : Finset (ι → Bool))
    (hG : ∀ x ∈ G, Q x = chi F univ x) (f : (ι → Bool) → F) :
    ∃ p ∈ lowDegree F ι (Fintype.card ι / 2 + D), ∀ x ∈ G, p x = f x :=
  exists_agree_of_phaseChar (ω := -1) (neg_ne_zero.2 one_ne_zero)
    (fun h => Invertible.ne_zero (2 : F) (by
      calc (2 : F) = 1 - (-1 : F) := by ring
        _ = 1 - 1 := by rw [h]
        _ = 0 := sub_self 1))
    hQ G hG f

/-- **Parity is far from low-degree functions.** A function of degree at most `D` agrees with the
parity of all coordinates on at most as many inputs as there are sets of at most `|ι| / 2 + D`
coordinates. -/
theorem card_agree_parityOn_univ_le [DecidableEq ι] [DecidableEq F] [Invertible (2 : F)] {D : ℕ}
    {P : (ι → Bool) → F} (hP : P ∈ lowDegree F ι D) :
    #{x | P x = bitVal F (parityOn univ x)} ≤
      #{S : Finset ι | #S ≤ Fintype.card ι / 2 + D} :=
  card_le_of_forall_exists_agree _ (exists_agree_of_parity (Q := 1 - 2 • P)
    (Submodule.sub_mem _ (one_mem_lowDegree D) (Submodule.smul_of_tower_mem _ 2 hP))
    {x | P x = bitVal F (parityOn univ x)} fun x hx => by
      rw [mem_filter] at hx
      rw [chi_eq_neg_one_pow_parityOn, neg_one_pow_toNat_eq_one_sub_two_mul_bitVal, ← hx.2]
      simp [two_mul])

/-- **Parity is far from low-degree functions.** A function of degree at most `D` agrees with
parity on at most as many inputs as there are sets of at most `n / 2 + D` coordinates. -/
theorem card_agree_parity_le [DecidableEq F] [Invertible (2 : F)] {n D : ℕ}
    {P : BitString n → F} (hP : P ∈ lowDegree F (Fin n) D) :
    #{x | P x = bitVal F (parity n x)} ≤ #{S : Finset (Fin n) | #S ≤ n / 2 + D} := by
  have h := card_agree_parityOn_univ_le hP
  rw [Fintype.card_fin] at h
  exact h

end Cslib.BitString
