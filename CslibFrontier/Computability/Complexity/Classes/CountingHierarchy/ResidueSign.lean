/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.PrimeCofactor
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DyadicSummation
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DyadicFirstFlag
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.SignParameters

/-!
# Integer signs from uniform modular residues

The general window operations consume only a residue evaluator, short binary cutoffs and
doubling limit, and a unary dyadic precision. Cofactors and weighted residues cost F_max(a,5),
the rounded sum costs one more level, and first-flag classification costs two more.
The represented integer, its magnitude bound `2^m`, and the full prime product are never
machine data. The same total evaluators serve every modulus and doubling index.

The `IntegerResidueAccess` application chooses the manuscript parameters and proves correctness
from the access contract, including zero, negative integers and excluded small primes.
The binary magnitude exponent and excluded-prime cutoff may have exponential values.

## Main definitions

* `Cslib.Complexity.residueWindowNumerator`: a natural dyadic numerator from weighted residues.
* `Cslib.Complexity.residueWindowSign`: bounded first-flag classification for generic parameters.
* `Cslib.Complexity.IntegerResidueAccess.primeWindowSign`: the manuscript-parameter application.

## Main results

* `Cslib.Complexity.CountingFunction.residueWindowSign_mem`: the general computational bound.
* `Cslib.Complexity.IntegerResidueAccess.primeWindowSign_eq_sign`: mathematical correctness.
* `Cslib.Complexity.IntegerResidueAccess.sign_mem_CountingFunction`: Proposition 2.6's bound.

## References

* [OpenAI2026CountingHierarchy], Section 2, Proposition 2.6 (Sign from residues).
  The proof uses the existing strict oracle-program and fixed-length majority-verifier levels.
  It does not establish an additional oracle-machine characterization or the ETR theorem.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Approximate weighted residues on the selected prime window using natural arithmetic.
The zero-masked sum has no input containing a full integer or full modulus product. -/
@[expose] noncomputable def residueWindowNumerator (Y L B : ℕ)
    (residue : ℕ → ℕ) (k : ℕ) : ℕ :=
  dyadicRangeSum B (Y + 1)
    (fun p => if primeWindowTest Y L p then
      primeWindowCoefficient Y L p k (residue p) else 0) id

/-- Total first-flag classifier with arbitrary window, precision and doubling limit.
Correct integer-sign behavior requires the numerical CRT conditions; the computational
certificate holds for all parameters. The endpoint includes `K`. -/
noncomputable def residueWindowSign (Y L B K : ℕ) (residue : ℕ → ℕ) : ℤ :=
  dyadicFirstFlagSign 8 B (K + 1) (residueWindowNumerator Y L B residue)

/-- The natural approximation is exactly the rational CRT approximation of its coefficients. -/
theorem residueWindowNumerator_eq_crt (Y L B k : ℕ) (residue : ℕ → ℕ) :
    (residueWindowNumerator Y L B residue k : ℚ) / (2 : ℚ) ^ B =
      Cslib.crtCircleApprox
        (fun p : ↥(Nat.primesLE Y \ Nat.primesLE L) => (p.val : ℤ)) B
        (fun p => (primeWindowCoefficient Y L p.val k (residue p.val) : ℤ)) := by
  classical
  have hs : Nat.primesLE Y \ Nat.primesLE L ⊆ Finset.range (Y + 1) := by
    intro p hp
    exact Finset.mem_range.mpr
      (Nat.lt_succ_of_le (Nat.mem_primesLE_sdiff_primesLE_iff.mp hp).2.2)
  unfold residueWindowNumerator
  simp only [primeWindowTest_eq_true_iff]
  rw [dyadicRangeSum_restrict_eq _ _ _ _ hs]
  exact Cslib.dyadicResidueNumerator_eq _ _ _

namespace CountingFunction

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

/-- Uniform residue access gives dyadic numerator access in F_(max(a,5)+1).
The primary instance is paired with one binary doubling index; all moduli use one evaluator. -/
theorem residueWindowNumerator_mem (D : Decoder enc) {Y L B : α → ℕ}
    {residue : α × ℕ → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hB : ComputableInPolyTime B enc encUnary)
    (hresidue : residue ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun (w, k) => residueWindowNumerator (Y w) (L w) (B w)
      (fun p => residue (w, p)) k) ∈
        CountingFunction (max a 5 + 1) (encPair enc encNat) encNat := by
  have hY' := hY.comp (ComputableInPolyTime.fst enc encNat)
  have hL' := hL.comp (ComputableInPolyTime.fst enc encNat)
  have hB' := hB.comp (ComputableInPolyTime.fst enc encNat)
  have hY'' := hY'.comp (ComputableInPolyTime.fst (encPair enc encNat) encNat)
  have hL'' := hL'.comp (ComputableInPolyTime.fst (encPair enc encNat) encNat)
  have hr := preprocess (input := encPair (encPair enc encNat) encNat) hresidue
    (g := fun x : (α × ℕ) × ℕ => (x.1.1, x.2)) (by fun_prop)
  have hk : ComputableInPolyTime (fun x : (α × ℕ) × ℕ => x.1.2)
      (encPair (encPair enc encNat) encNat) encNat := by fun_prop
  have hc := primeWindowCoefficient_mem (Decoder.pair (Decoder.pair D Decoder.nat) Decoder.nat)
    hY'' hL'' (ComputableInPolyTime.snd _ _) hk hr
  have hwindow := primeWindowTest_mem hY'' hL'' (ComputableInPolyTime.snd _ _)
  have hnum := ite (mono (by omega : 1 ≤ max a 5) hwindow) hc
    (of_polyTime (ComputableInPolyTime.const 0))
  exact dyadicRangeSum_mem (Decoder.pair D Decoder.nat) hnum
    (of_polyTime (ComputableInPolyTime.snd _ _)) hB'
    (ComputableInPolyTime.binary_add' hY' (ComputableInPolyTime.const 1))

/-- Uniform residue access, binary window/limit preparation and unary precision give the
total window classifier in F_(max(a,5)+3). Correctness is independent of this cost certificate. -/
theorem residueWindowSign_mem (D : Decoder enc) {Y L B K : α → ℕ}
    {residue : α × ℕ → ℕ}
    (hY : ComputableInPolyTime Y enc encNat)
    (hL : ComputableInPolyTime L enc encNat)
    (hB : ComputableInPolyTime B enc encUnary)
    (hK : ComputableInPolyTime K enc encNat)
    (hresidue : residue ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => residueWindowSign (Y w) (L w) (B w) (K w)
      (fun p => residue (w, p))) ∈ CountingFunction (max a 5 + 3) enc encIntBin :=
  dyadicFirstFlagSign_mem D (residueWindowNumerator_mem D hY hL hB hresidue)
    (ComputableInPolyTime.const 8) hB
    (ComputableInPolyTime.binary_add' hK (ComputableInPolyTime.const 1))

end CountingFunction

namespace IntegerResidueAccess

variable {α : Type} {X : α → ℤ}

/-- Recover a sign using the manuscript window derived from the access bound and an excluded
prime cutoff. Only bound/residue operations are read from the access record. -/
noncomputable def primeWindowSign (R : IntegerResidueAccess X) (L : α → ℕ) (w : α) : ℤ :=
  let Y := Cslib.PrimeWindowSign.cutoff (R.magnitudeExponent w) (L w)
  residueWindowSign Y (L w) (Y.size + 10) (Y * Y.size + 1)
    (fun p => R.residue (w, p))

/-- The computed window classifier has the asserted level on every input, even before
the residue correctness domain is checked. All query sizes follow from strict composition. -/
theorem primeWindowSign_mem_CountingFunction {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) (R : IntegerResidueAccess X) (hR : R.InCountingFunction a enc)
    {L : α → ℕ} (hL : ComputableInPolyTime L enc encNat) :
    R.primeWindowSign L ∈ CountingFunction (max a 5 + 3) enc encIntBin :=
  CountingFunction.residueWindowSign_mem D
    (Cslib.PrimeWindowSign.cutoff_polyTime hR.1 hL) hL
    (Cslib.PrimeWindowSign.precision_polyTime hR.1 hL)
    (Cslib.PrimeWindowSign.doublingLimit_polyTime hR.1 hL) hR.2

/-- Correctness for all signs, including zero. Only prime moduli in the stated window need
belong to the access domain; no admissibility recognizer is used by the algorithm. -/
theorem primeWindowSign_eq_sign (R : IntegerResidueAccess X) (L : α → ℕ) (w : α)
    (hcover : ∀ p ∈ Cslib.PrimeWindowSign.primes (R.magnitudeExponent w) (L w),
      R.admissible w p) : R.primeWindowSign L w = (X w).sign := by
  let m := R.magnitudeExponent w
  let Lw := L w
  let Y := Cslib.PrimeWindowSign.cutoff m Lw
  let B := Y.size + 10
  let K := Y * Y.size + 1
  let N := residueWindowNumerator Y Lw B (fun p => R.residue (w, p))
  let c : ℕ → Cslib.PrimeWindowSign.primes m Lw → ℤ := fun k p =>
    primeWindowCoefficient Y Lw p.val k (R.residue (w, p.val))
  have hc (k : ℕ) (p : Cslib.PrimeWindowSign.primes m Lw) :
      c k p * Cslib.crtCofactor (Cslib.PrimeWindowSign.modulus m Lw) p ≡
        (2 : ℤ) ^ k * X w [ZMOD Cslib.PrimeWindowSign.modulus m Lw p] :=
    primeWindowCoefficient_modEq_subtype Y Lw k _ p
      (R.residue_modEq (hcover p.val p.property))
  have happrox (k : ℕ) : (N k : ℚ) / (2 : ℚ) ^ B =
      Cslib.crtCircleApprox (Cslib.PrimeWindowSign.modulus m Lw) B (c k) :=
    residueWindowNumerator_eq_crt Y Lw B k _
  have hbound : |X w| ≤ (2 : ℤ) ^ m := by
    have hb : ((X w).natAbs : ℤ) ≤ ((2 ^ m : ℕ) : ℤ) := by
      exact_mod_cast R.magnitude_le w
    simpa only [Int.natCast_natAbs, Nat.cast_pow, Nat.cast_ofNat] using hb
  change dyadicFirstFlagSign 8 B (K + 1) N = (X w).sign
  by_cases hzero : X w = 0
  · rw [hzero, Int.sign_zero]
    apply (dyadicFirstFlagSign_eq_zero_iff (by decide : 0 < 8) N).mpr
    have hnone (k : ℕ) : ¬ Cslib.CircleFlag (1 / 8) ((N k : ℚ) / (2 : ℚ) ^ B) := by
      rw [happrox]
      apply Cslib.PrimeWindowSign.not_flag_zero_of_coefficients m Lw
      intro p
      simpa only [hzero, mul_zero] using hc k p
    constructor <;> rintro ⟨k, _, hfirst, _⟩ <;> exact hnone k hfirst.1
  · obtain ⟨k, hk, hfirst, hpos, hneg⟩ :=
      Cslib.PrimeWindowSign.firstCircleFlag_sign_of_coefficients m Lw c (X w)
        hbound hzero (fun k _ p => hc k p)
    have hf : Cslib.FirstCircleFlag (1 / 8)
        (fun j => (N j : ℚ) / (2 : ℚ) ^ B) k := by
      simpa only [Cslib.FirstCircleFlag, happrox] using hfirst
    have hk' : k < K + 1 := Nat.lt_succ_of_le hk
    rcases lt_or_gt_of_ne hzero with hn | hp
    · rw [Int.sign_eq_neg_one_of_neg hn]
      apply (dyadicFirstFlagSign_eq_neg_one_iff (by decide : 0 < 8) N).mpr
      refine ⟨k, hk', hf, ?_⟩
      rw [happrox]
      exact hneg.mp hn
    · rw [Int.sign_eq_one_of_pos hp]
      apply (dyadicFirstFlagSign_eq_one_iff (by decide : 0 < 8) N).mpr
      refine ⟨k, hk', hf, ?_⟩
      rw [happrox]
      exact hpos.mp hp

/-- Sign from modular residues, with the manuscript's F_(max(a,5)+3) bound.
The bound exponent and excluded cutoff are polynomial-time binary values and may be
exponentially large. Residues are supplied by one fixed F_a evaluator; every prime in the
specified window must be admissible. No full integer or prime product is constructed. -/
theorem sign_mem_CountingFunction {enc : α ↪ List Bool} {a : ℕ}
    (D : Decoder enc) (R : IntegerResidueAccess X) (hR : R.InCountingFunction a enc)
    {L : α → ℕ} (hL : ComputableInPolyTime L enc encNat)
    (hcover : ∀ w p, p ∈ Cslib.PrimeWindowSign.primes (R.magnitudeExponent w) (L w) →
      R.admissible w p) :
    (fun w => (X w).sign) ∈ CountingFunction (max a 5 + 3) enc encIntBin := by
  have h := primeWindowSign_mem_CountingFunction D R hR hL
  have heq : R.primeWindowSign L = (fun w => (X w).sign) :=
    funext fun w => primeWindowSign_eq_sign R L w (hcover w)
  exact heq ▸ h

end IntegerResidueAccess
end Cslib.Complexity
