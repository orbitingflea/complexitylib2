/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import CslibFrontier.Foundations.NumberTheory.DyadicResidues
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv

/-!
# Total dyadic summation on binary intervals

`dyadicRangeSum` scales each natural numerator by `2 ^ B`, divides by its denominator,
sums below a binary endpoint, and reduces modulo `2 ^ B`. A zero denominator contributes
zero by natural division's total convention. No rational or represented integer is program data.

The precision is polynomial-time **unary**, so constructing the binary scale is charged.
Uniform F_a numerator and denominator evaluators give an F_(a+1) sum. Masking the numerator
outside a finite subset recovers the mathematical `Cslib.dyadicResidueNumerator` exactly.

## Main definitions

* `Cslib.Complexity.dyadicRangeSum`: total natural dyadic numerator summation.

## Main results

* `Cslib.Complexity.CountingFunction.dyadicRangeSum_mem`: one-level summation bound.
* `Cslib.Complexity.dyadicRangeSum_restrict_eq`: restriction to a finite residue set.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Finset

/-- Total dyadic numerator sum below `r`, reduced modulo `2 ^ B`.
A denominator of zero contributes zero, including at index zero. -/
@[expose] def dyadicRangeSum (B r : ℕ) (num den : ℕ → ℕ) : ℕ :=
  (∑ i ∈ range r, (2 ^ B * num i) / den i) % 2 ^ B

/-- Zero-masking outside a finite subset agrees with the finite residue numerator.
The denominators are the indices themselves; index zero uses the same total division default. -/
theorem dyadicRangeSum_restrict_eq (s : Finset ℕ) (B r : ℕ) (c : ℕ → ℕ)
    (hs : s ⊆ range r) :
    dyadicRangeSum B r (fun i => if i ∈ s then c i else 0) id =
      Cslib.dyadicResidueNumerator s B c := by
  unfold dyadicRangeSum Cslib.dyadicResidueNumerator
  congr 1
  calc
    (∑ i ∈ range r, (2 ^ B * (if i ∈ s then c i else 0)) / i) =
        ∑ i ∈ s, (2 ^ B * (if i ∈ s then c i else 0)) / i :=
      (sum_subset hs (fun i _ hi => by simp [hi])).symm
    _ = ∑ i ∈ s, (2 ^ B * c i) / i :=
      sum_congr rfl fun i hi => by rw [ite_eq_left hi]

namespace CountingFunction

/-- Uniform F_a numerators and denominators yield an F_(a+1) dyadic numerator sum.
Unary precision pays for scale construction; the binary endpoint may have exponential value.
Division, intermediate arithmetic, summation and the final binary remainder are all charged. -/
theorem dyadicRangeSum_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) {B r : α → ℕ} {num den : α × ℕ → ℕ}
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hB : ComputableInPolyTime B enc encUnary) (hr : ComputableInPolyTime r enc encNat) :
    (fun x => dyadicRangeSum (B x) (r x) (fun i => num (x, i)) (fun i => den (x, i))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hscale : ComputableInPolyTime (fun x => 2 ^ B x) enc encNat :=
    ComputableInPolyTime.binary_two_pow.comp hB
  have hscale' : ComputableInPolyTime (fun x : α × ℕ => 2 ^ B x.1)
      (encPair enc encNat) encNat := hscale.comp (ComputableInPolyTime.fst _ _)
  have hterm := map (prod (nat_mul (of_polyTime hscale') hnum) hden)
    ComputableInPolyTime.binary_div
  exact nat_mod (sum_range D hterm hr) (of_polyTime hscale)

end CountingFunction
end Cslib.Complexity
