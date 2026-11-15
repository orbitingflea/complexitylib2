/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Aggregation
public import Mathlib.Data.Nat.Prime.Defs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Nat.Prime.Basic

/-!
# Uniform primality at the first counting function level

A universal short-index divisor check certifies primality in F_1. The input is binary,
including zero and one; the evaluator uses total binary remainder. No primality oracle
or uncharged arithmetic procedure is assumed.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- The total Boolean primality predicate on binary naturals. -/
@[expose] def primeTest (p : ℕ) : Bool := decide p.Prime

/-- Check one bounded-divisor candidate, rejecting moduli below two and ignoring candidates
outside the proper-divisor interval. The index is a binary word. -/
def divisorIndexTest (x : ℕ × List Bool) : Bool :=
  let (p, word) := x
  let d := BitString.binaryValue word
  decide (2 ≤ p ∧ (d < 2 ∨ p ≤ d ∨ p % d ≠ 0))

/-- The shared divisor check has an ordinary polynomial-time binary certificate. -/
theorem divisorIndexTest_polyTime :
    ComputableInPolyTime divisorIndexTest (encPair encNat encBits) encBool := by
  have hp := ComputableInPolyTime.fst encNat encBits
  have hd : ComputableInPolyTime (fun x : ℕ × List Bool => BitString.binaryValue x.2)
      (encPair encNat encBits) encNat := by fun_prop
  have hrem := ComputableInPolyTime.binary_mod.comp (hp.prod hd)
  exact ComputableInPolyTime.decide_and (ComputableInPolyTime.binary_le' (.const 2) hp)
    (ComputableInPolyTime.decide_or (ComputableInPolyTime.binary_lt' hd (.const 2))
      (ComputableInPolyTime.decide_or (ComputableInPolyTime.binary_le' hp hd)
        (ComputableInPolyTime.decide_ne hrem (.const 0))))

/-- One fixed-width universal pass of the shared divisor check characterizes primality. -/
theorem prime_iff_divisorIndices (p : ℕ) :
    p.Prime ↔ ∀ w : Fin p.size → Bool, divisorIndexTest (p, List.ofFn w) = true := by
  simp only [divisorIndexTest, decide_eq_true_eq]
  constructor
  · intro hp w
    refine ⟨hp.two_le, ?_⟩
    by_cases hsmall : BitString.binaryValue (List.ofFn w) < 2
    · exact Or.inl hsmall
    · by_cases hlarge : p ≤ BitString.binaryValue (List.ofFn w)
      · exact Or.inr (Or.inl hlarge)
      · refine Or.inr (Or.inr ?_)
        intro hzero
        exact (Nat.prime_def_lt'.mp hp).2 _ (by omega) (by omega)
          (Nat.dvd_of_mod_eq_zero hzero)
  · intro h
    have hp2 := (h (fun _ => false)).1
    apply Nat.prime_def_lt'.mpr
    refine ⟨hp2, ?_⟩
    intro d hd hdp hdvd
    obtain ⟨w, hw⟩ := BitString.exists_binaryValue_eq (hdp.trans (Nat.lt_size_self p))
    have hchecks := (h w).2
    rw [hw, Nat.mod_eq_zero_of_dvd hdvd] at hchecks
    omega

/-- One uniform universal divisor test computes primality in F_1, with binary input. -/
theorem primeTest_mem_CountingFunction : primeTest ∈ CountingFunction 1 encNat encBool := by
  have h := CountingFunction.forall_bits Decoder.nat
    (CountingFunction.of_polyTime (a := 0) divisorIndexTest_polyTime)
    ComputableInPolyTime.binary_size
  convert h using 1
  funext p
  simp only [primeTest, prime_iff_divisorIndices]

end Cslib.Complexity
