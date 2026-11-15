/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation
public import CslibFrontier.Foundations.Data.BitString.WeightedEnumeration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Counting-level sums over binary bounds

A binary polynomial-time endpoint may have exponential value. Enumerating its binary width
through one uniform evaluator still costs one counting level. These rules include the empty
interval and avoid an explicit list of its elements.

## Main results

* `Cslib.Complexity.CountingFunction.sum_range`: natural sums up to a short binary bound.
* `Cslib.Complexity.CountingFunction.sum_range_int`: signed sums with the same bound.
-/

public section

namespace Cslib.Complexity.CountingFunction

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

private theorem binaryIndexEvaluator_mem {β : Type} [Zero β] {out : β ↪ List Bool}
    {f : α × ℕ → β} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encNat) out)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x : α × List Bool => if Cslib.BitString.binaryValue x.2 < r x.1
      then f (x.1, Cslib.BitString.binaryValue x.2) else 0) ∈
        CountingFunction a (encPair enc encBits) out := by
  have hvalue := preprocess (input := encPair enc encBits) hf
    (g := fun x : α × List Bool => (x.1, Cslib.BitString.binaryValue x.2)) (by fun_prop)
  have hguard : ComputableInPolyTime
      (fun x : α × List Bool => decide (Cslib.BitString.binaryValue x.2 < r x.1))
      (encPair enc encBits) encBool := by fun_prop
  simpa only [decide_eq_true_eq] using
    ite (of_polyTime hguard) hvalue (of_polyTime (ComputableInPolyTime.const 0))

/-- Summation below a polynomial-bit binary endpoint costs one function level. -/
theorem sum_range (D : Decoder enc) {f : α × ℕ → ℕ} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encNat) encNat)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x => ∑ i ∈ Finset.range (r x), f (x, i)) ∈
      CountingFunction (a + 1) enc encNat := by
  have h := sum_bits D (binaryIndexEvaluator_mem hf hr)
    (ComputableInPolyTime.binary_size.comp hr)
  convert h using 1
  funext x
  exact (Cslib.BitString.sum_binaryValue_lt (Nat.lt_size_self (r x)).le
    (fun i => f (x, i))).symm

/-- Signed summation below a short binary endpoint has the same one-level cost. -/
theorem sum_range_int (D : Decoder enc) {f : α × ℕ → ℤ} {r : α → ℕ}
    (hf : f ∈ CountingFunction a (encPair enc encNat) encIntBin)
    (hr : ComputableInPolyTime r enc encNat) :
    (fun x => ∑ i ∈ Finset.range (r x), f (x, i)) ∈
      CountingFunction (a + 1) enc encIntBin := by
  have h := sum_bits_int D (binaryIndexEvaluator_mem hf hr)
    (ComputableInPolyTime.binary_size.comp hr)
  convert h using 1
  funext x
  exact (Cslib.BitString.sum_binaryValue_lt (Nat.lt_size_self (r x)).le
    (fun i => f (x, i))).symm

end Cslib.Complexity.CountingFunction
