/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueSign
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode

/-!
# Residue access without an explicit integer expansion

The family `2^(2^n)` has exponentially many bits on unary input `n`. Its logarithmic magnitude
bound has only `n + 1` binary bits, and its residues are ordinary polynomial-time modular powers.
Explicit signed integers provide complementary zero and negative clients.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.ResidueSign

open Cslib Cslib.Complexity Turing.MultiTapeTM

def huge (n : ℕ) : ℤ := (2 : ℤ) ^ (2 ^ n)

def hugeAccess : IntegerResidueAccess huge where
  magnitudeExponent := fun n => 2 ^ n
  admissible := fun _ p => 0 < p
  modulus_pos := fun _ _ hp => hp
  residue := fun (n, p) => powMod p 2 (2 ^ n)
  magnitude_le := by
    intro n
    simp [huge]
  residue_eq := by
    intro n p hp
    change powMod p 2 (2 ^ n) = (((2 : ℤ) ^ (2 ^ n) % (p : ℤ)).toNat)
    rw [powMod_of_ne_zero (by omega : p ≠ 0)]
    have hx : (2 : ℤ) ^ (2 ^ n) = ((2 ^ (2 ^ n) : ℕ) : ℤ) := by norm_cast
    rw [hx, ← Int.natCast_emod, Int.toNat_natCast]

theorem hugeAccess_level : hugeAccess.InCountingFunction 0 encUnary := by
  constructor
  · exact ComputableInPolyTime.binary_two_pow
  · apply CountingFunction.of_polyTime
    exact computableInPolyTime_powMod (ComputableInPolyTime.snd _ _)
      (ComputableInPolyTime.const 2)
      (ComputableInPolyTime.binary_two_pow.comp (ComputableInPolyTime.fst _ _))

example : hugeAccess.residue (3, 17) = 1 := by decide
example : hugeAccess.magnitudeExponent 10 = 1024 := by decide

def explicitAccess : IntegerResidueAccess (fun z : ℤ => z) where
  magnitudeExponent := fun z => z.natAbs.size
  admissible := fun _ p => 0 < p
  modulus_pos := fun _ _ hp => hp
  residue := fun (z, p) => (z % (p : ℤ)).toNat
  magnitude_le := fun z => (Nat.lt_size_self z.natAbs).le
  residue_eq := fun _ _ _ => rfl

theorem explicitAccess_level : explicitAccess.InCountingFunction 0 encIntBin := by
  constructor
  · exact ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.binary_size.comp ComputableInPolyTime.intBin_natAbs)
  · exact CountingFunction.of_polyTime ComputableInPolyTime.intBin_emodNat

example : explicitAccess.residue (-13, 5) = 2 := by decide
example : explicitAccess.residue (0, 5) = 0 := by decide

private theorem explicitSign_correct (z : ℤ) :
    explicitAccess.primeWindowSign Int.natAbs z = z.sign := by
  apply IntegerResidueAccess.primeWindowSign_eq_sign
  intro p hp
  change 0 < p
  exact (Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩).pos

example : explicitAccess.primeWindowSign Int.natAbs (-13) = -1 := by
  rw [explicitSign_correct]
  decide

example : explicitAccess.primeWindowSign Int.natAbs 0 = 0 := by
  rw [explicitSign_correct]
  decide

example : explicitAccess.primeWindowSign Int.natAbs 19 = 1 := by
  rw [explicitSign_correct]
  decide

example : (fun z : ℤ => z.sign) ∈ CountingFunction 8 encIntBin encIntBin := by
  apply IntegerResidueAccess.sign_mem_CountingFunction Decoder.intBin explicitAccess
    explicitAccess_level ComputableInPolyTime.intBin_natAbs
  intro z p hp
  change 0 < p
  exact (Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩).pos

/-- This applies the full algorithm to a family with exponentially many output bits. -/
example (n : ℕ) : hugeAccess.primeWindowSign (fun _ => 0) n = 1 := by
  have h := hugeAccess.primeWindowSign_eq_sign (fun _ => 0) n (fun p hp =>
    (Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩).pos)
  rw [h]
  exact Int.sign_eq_one_of_pos (by unfold huge; positivity)

example : (fun n => (huge n).sign) ∈ CountingFunction 8 encUnary encIntBin := by
  apply IntegerResidueAccess.sign_mem_CountingFunction Decoder.unary hugeAccess
    hugeAccess_level (ComputableInPolyTime.const 0)
  intro n p hp
  exact (Cslib.PrimeWindowSign.prime _ _ ⟨p, hp⟩).pos

/-- A product followed by a sum realizes the conservative F_8 → F_13 bookkeeping. -/
example {α : Type} {enc : α ↪ List Bool} (D : Decoder enc)
    {f : (α × List Bool) × List Bool → ℕ} {p b r : α → ℕ}
    (hf : f ∈ CountingFunction 8 (encPair (encPair enc encBits) encBits) encNat)
    (hp : ComputableInPolyTime p enc encNat)
    (hb : ComputableInPolyTime b enc encUnary)
    (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => ∑ i : Fin (r x) → Bool,
      primeFieldProduct (p x) (b x) (fun j => f ((x, List.ofFn i), j))) ∈
        CountingFunction 13 enc encNat :=
  CountingFunction.sum_bits D
    (CountingFunction.prod_primeField_bits (Decoder.pair D Decoder.bits) hf
      (hp.comp (ComputableInPolyTime.fst _ _))
      (hb.comp (ComputableInPolyTime.fst _ _))) hr

/-- Nested modular products may use different inner moduli, giving F_13 → F_21. -/
example {α : Type} {enc : α ↪ List Bool} (D : Decoder enc)
    {f : (α × List Bool) × List Bool → ℕ}
    {innerPrime innerWidth : α × List Bool → ℕ} {p r : α → ℕ}
    (hf : f ∈ CountingFunction 13 (encPair (encPair enc encBits) encBits) encNat)
    (hip : ComputableInPolyTime innerPrime (encPair enc encBits) encNat)
    (hiw : ComputableInPolyTime innerWidth (encPair enc encBits) encUnary)
    (hp : ComputableInPolyTime p enc encNat) (hr : ComputableInPolyTime r enc encUnary) :
    (fun x => primeFieldProduct (p x) (r x) (fun i =>
      primeFieldProduct (innerPrime (x, i)) (innerWidth (x, i)) (fun j => f ((x, i), j)))) ∈
        CountingFunction 21 enc encNat :=
  CountingFunction.prod_primeField_bits D
    (CountingFunction.prod_primeField_bits (Decoder.pair D Decoder.bits) hf hip hiw) hp hr

/-- A uniform F_21 residue component yields signs at 24, choice at 25 and a language at 26.
No characteristic-coefficient computation or real-feasibility theorem is assumed or asserted. -/
example {α : Type} {enc : α ↪ List Bool} (D : Decoder enc)
    {X : α × List Bool → ℤ} (R : IntegerResidueAccess X)
    (hR : R.InCountingFunction 21 (encPair enc encBits)) {L : α × List Bool → ℕ}
    (hL : ComputableInPolyTime L (encPair enc encBits) encNat)
    (hcover : ∀ w p, p ∈ Cslib.PrimeWindowSign.primes (R.magnitudeExponent w) (L w) →
      R.admissible w p)
    {r : α → ℕ} (hr : ComputableInPolyTime r enc encUnary) :
    {x | ∃ i : List Bool, i.length = r x ∧ 0 < X (x, i)} ∈ CountingLevel 26 enc := by
  classical
  have hs : (fun w => (X w).sign) ∈
      CountingFunction 24 (encPair enc encBits) encIntBin :=
    IntegerResidueAccess.sign_mem_CountingFunction (Decoder.pair D Decoder.bits) R hR hL hcover
  have hpos : (fun w => decide (0 < X w)) ∈
      CountingFunction 24 (encPair enc encBits) encBool := by
    simpa only [Int.sign_pos_iff] using
      CountingFunction.map hs ComputableInPolyTime.intBin_isPos
  have hex : (fun x => decide (∃ i : List Bool, i.length = r x ∧ 0 < X (x, i))) ∈
      CountingFunction 25 enc encBool := by
    simpa only [decide_eq_true_eq] using CountingFunction.exists_bits D hpos hr
  simpa only [decide_eq_true_eq] using CountingFunction.decision hex

end CslibFrontierTests.ResidueSign
