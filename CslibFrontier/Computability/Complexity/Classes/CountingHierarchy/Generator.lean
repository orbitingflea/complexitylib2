/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Primality
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Foundations.Data.BitString.List.Binary

/-!
# Testing generators of prime fields at the first counting function level

`generatorTest (p, g)` accepts exactly a prime modulus `p` and a positive canonical representative
`g < p` of a primitive root. It is total on every pair of binary naturals. Primality is checked
by universally testing possible divisors, and generator status by universally testing the
smaller positive exponents. One bitstring of width `Nat.size p` supplies either candidate.
Thus the evaluator is polynomial-time, though its domain can be exponential, and one application
of short-index universal quantification places the test in F_1. No primality or discrete-log
oracle is assumed. Modular exponentiation uses the existing certified square-and-multiply API.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

private abbrev generatorChecks (p g d : ℕ) : Prop :=
  0 < g ∧ g < p ∧ (d = 0 ∨ p - 1 ≤ d ∨ powMod p g d ≠ 1)

private def generatorIndexTest : (ℕ × ℕ) × List Bool → Bool
  | ((p, g), w) => divisorIndexTest (p, w) &&
      decide (generatorChecks p g (BitString.binaryValue w))

open Classical in
/-- Test prime-field primitive roots on binary modulus/base pairs. Every malformed pair,
including modulus zero or one and noncanonical representatives, is rejected. -/
noncomputable def generatorTest (x : ℕ × ℕ) : Bool :=
  decide (∀ w : Fin (Nat.size x.1) → Bool, generatorIndexTest (x, List.ofFn w) = true)

private theorem computableInPolyTime_generatorIndexTest :
    ComputableInPolyTime generatorIndexTest
      (encPair (encPair encNat encNat) encBits) encBool := by
  have hdiv := divisorIndexTest_polyTime.comp
    (show ComputableInPolyTime (fun x : (ℕ × ℕ) × List Bool => (x.1.1, x.2))
      (encPair (encPair encNat encNat) encBits) (encPair encNat encBits) by fun_prop)
  have hpow : ComputableInPolyTime
      (fun x : (ℕ × ℕ) × List Bool => powMod x.1.1 x.1.2 (BitString.binaryValue x.2))
      (encPair (encPair encNat encNat) encBits) encNat :=
    computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun pair : ((ℕ × ℕ) × List Bool) × ℕ =>
        let ((p, g), word) := pair.1
        let d := BitString.binaryValue word
        decide (0 < g ∧ g < p ∧ (d = 0 ∨ p - 1 ≤ d ∨ pair.2 ≠ 1)))
      (encPair (encPair (encPair encNat encNat) encBits) encNat) encBool := by
    have hp : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List Bool) × ℕ => x.1.1.1)
        (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
    have hg : ComputableInPolyTime (fun x : ((ℕ × ℕ) × List Bool) × ℕ => x.1.1.2)
        (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
    have hd : ComputableInPolyTime
        (fun x : ((ℕ × ℕ) × List Bool) × ℕ => BitString.binaryValue x.1.2)
        (encPair (encPair (encPair encNat encNat) encBits) encNat) encNat := by fun_prop
    have hpred := ComputableInPolyTime.binary_sub' hp (ComputableInPolyTime.const 1)
    exact ComputableInPolyTime.decide_and (ComputableInPolyTime.binary_lt' (.const 0) hg)
      (ComputableInPolyTime.decide_and (ComputableInPolyTime.binary_lt' hg hp)
        (ComputableInPolyTime.decide_or
          (ComputableInPolyTime.of_tidy (hd.tidy.decide_eq' (.const 0)))
          (ComputableInPolyTime.decide_or (ComputableInPolyTime.binary_le' hpred hd)
            (ComputableInPolyTime.decide_ne (ComputableInPolyTime.snd _ _) (.const 1)))))
  exact ComputableInPolyTime.bool_and.comp
    (hdiv.prod (hpost.comp (ComputableInPolyTime.id'.prod hpow)))

/-- A single universal short-index check puts the complete generator test in F_1.
All arithmetic and prime-divisor tests are performed by its one polynomial-time evaluator. -/
theorem generatorTest_mem_CountingFunction :
    generatorTest ∈ CountingFunction 1 (encPair encNat encNat) encBool := by
  have hwidth : ComputableInPolyTime (fun x : ℕ × ℕ => Nat.size x.1)
      (encPair encNat encNat) encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.fst encNat encNat)
  exact CountingFunction.forall_bits (Decoder.pair Decoder.nat Decoder.nat)
    (CountingFunction.of_polyTime computableInPolyTime_generatorIndexTest) hwidth

private theorem generatorTest_iff_checks (p g : ℕ) :
    generatorTest (p, g) = true ↔
      p.Prime ∧ 0 < g ∧ g < p ∧
        (∀ d, 0 < d → d < p - 1 → powMod p g d ≠ 1) := by
  classical
  change decide (∀ w : Fin (Nat.size p) → Bool,
    (divisorIndexTest (p, List.ofFn w) &&
      decide (generatorChecks p g (BitString.binaryValue (List.ofFn w)))) = true) = true ↔ _
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  constructor
  · intro h
    have hp := (prime_iff_divisorIndices p).mpr (fun w => (h w).1)
    have hcheck (d : ℕ) (hd : d < 2 ^ Nat.size p) : generatorChecks p g d := by
      obtain ⟨w, hw⟩ := BitString.exists_binaryValue_eq hd
      simpa only [hw] using (h w).2
    obtain ⟨hg, hgp, _⟩ := hcheck 0 (by positivity)
    refine ⟨hp, hg, hgp, ?_⟩
    intro d hd hdp
    have hc := (hcheck d ((by omega : d < p).trans (Nat.lt_size_self p))).2.2
    exact hc.resolve_left (by omega) |>.resolve_left (by omega)
  · rintro ⟨hp, hg, hgp, hexp⟩ w
    let d := BitString.binaryValue (List.ofFn w)
    refine ⟨(prime_iff_divisorIndices p).mp hp w, hg, hgp, ?_⟩
    by_cases hd : d = 0
    · exact Or.inl hd
    · by_cases hdp : p - 1 ≤ d
      · exact Or.inr (Or.inl hdp)
      · exact Or.inr (Or.inr (hexp d (by omega) (by omega)))

private theorem powMod_eq_one_iff {p : ℕ} (hp : p.Prime) (g e : ℕ) :
    powMod p g e = 1 ↔ (g : ZMod p) ^ e = 1 := by
  rw [powMod_of_ne_zero hp.ne_zero]
  simpa only [Nat.cast_pow, Nat.cast_one, Nat.mod_eq_of_lt hp.one_lt] using
    (ZMod.natCast_eq_natCast_iff' (g ^ e) 1 p).symm

/-- The total binary test recognizes precisely canonical primitive roots of prime fields.
In particular the two-element field accepts its generator one, while all malformed moduli
are rejected. This characterization has no computational assumptions. -/
theorem generatorTest_eq_true_iff (p g : ℕ) :
    generatorTest (p, g) = true ↔
      p.Prime ∧ 0 < g ∧ g < p ∧ IsPrimitiveRoot (g : ZMod p) (p - 1) := by
  rw [generatorTest_iff_checks]
  constructor
  · rintro ⟨hp, hg, hgp, hexp⟩
    let : Fact p.Prime := ⟨hp⟩
    have hg0 : (g : ZMod p) ≠ 0 := by
      rw [ne_eq, ZMod.natCast_eq_zero_iff]
      exact Nat.not_dvd_of_pos_of_lt hg hgp
    refine ⟨hp, hg, hgp, (IsPrimitiveRoot.iff (by omega : 0 < p - 1)).mpr
      ⟨ZMod.pow_card_sub_one_eq_one hg0, ?_⟩⟩
    intro e he hep heq
    exact hexp e he hep ((powMod_eq_one_iff hp g e).mpr heq)
  · rintro ⟨hp, hg, hgp, hroot⟩
    refine ⟨hp, hg, hgp, ?_⟩
    intro e he hep heq
    exact hroot.pow_ne_one_of_pos_of_lt (by omega) hep
      ((powMod_eq_one_iff hp g e).mp heq)

/-- On canonical representatives of a prime field, the total test is exactly membership in
the finite set of multiplicative generators. -/
theorem generatorTest_eq_true_iff_mem {p : ℕ} [Fact p.Prime] {g : ℕ} (hg : g < p) :
    generatorTest (p, g) = true ↔ (g : ZMod p) ∈ primitiveRoots (p - 1) (ZMod p) := by
  have hp : p.Prime := Fact.out
  have hp2 := hp.two_le
  rw [generatorTest_eq_true_iff, mem_primitiveRoots (by omega : 0 < p - 1)]
  constructor
  · exact fun h => h.2.2.2
  · intro h
    have hgpos : 0 < g := by
      by_contra hn
      have hz : g = 0 := by omega
      exact h.ne_zero (by omega) (by simp only [hz, Nat.cast_zero])
    exact ⟨hp, hgpos, hg, h⟩

/-- Composite and malformed moduli reject every proposed generator. -/
theorem generatorTest_ne_true_of_not_prime {p g : ℕ} (hp : ¬p.Prime) :
    generatorTest (p, g) ≠ true := by
  exact fun h => hp ((generatorTest_eq_true_iff p g).mp h).1

end Cslib.Complexity
