/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Arithmetic
public import CslibFrontier.Foundations.NumberTheory.FiniteField.GeneratorProducts
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-!
# Total logarithm sums in prime fields

Sum every exponent below `p - 1` whose power matches the requested residue. At a primitive root
and nonzero target, uniqueness makes this sum the discrete logarithm. On all other inputs it
still defines a total polynomial-bit output. Short-index summation certifies this operation in
F_1 without a generator, factoring, or discrete-logarithm oracle.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- Sum matching exponents below `p - 1`, reducing the target modulo `p`. This is total for every
modulus, base and target; its logarithm specification requires a primitive prime-field base. -/
@[expose] def modularLogSum (p g x : ℕ) : ℕ :=
  ∑ e ∈ Finset.range (p - 1), if Turing.MultiTapeTM.powMod p g e = x % p then e else 0

/-- The natural matching-exponent sum agrees with its prime-field algebraic counterpart. -/
theorem modularLogSum_eq_generatorLogSum {p : ℕ} (hp : p ≠ 0) (g x : ℕ) :
    modularLogSum p g x = ZMod.generatorLogSum p (g : ZMod p) (x : ZMod p) := by
  unfold modularLogSum ZMod.generatorLogSum
  apply Finset.sum_congr rfl
  intro e _
  have h : Turing.MultiTapeTM.powMod p g e = x % p ↔ (g : ZMod p) ^ e = (x : ZMod p) := by
    rw [powMod_of_ne_zero hp]
    simpa only [Nat.cast_pow] using (ZMod.natCast_eq_natCast_iff' (g ^ e) x p).symm
  simp only [h]

/-- Computing a logarithm sum from binary modulus, base and target takes one function level.
Its range endpoint is short even when its value is exponential. -/
theorem modularLogSum_mem_CountingFunction :
    (fun (p, g, x) => modularLogSum p g x) ∈
      CountingFunction 1 encNat3 encNat := by
  have hp : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => x.1) encNat3 encNat := by
    fun_prop
  have hg : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => x.2.1) encNat3 encNat := by
    fun_prop
  have hx : ComputableInPolyTime (fun x : ℕ × ℕ × ℕ => x.2.2) encNat3 encNat := by
    fun_prop
  have hpower : ComputableInPolyTime
      (fun x : (ℕ × ℕ × ℕ) × ℕ =>
        Turing.MultiTapeTM.powMod x.1.1 x.1.2.1 x.2)
      (encPair encNat3 encNat) encNat :=
    computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)
  have htarget : ComputableInPolyTime
      (fun x : (ℕ × ℕ × ℕ) × ℕ => x.1.2.2 % x.1.1)
      (encPair encNat3 encNat) encNat :=
    ComputableInPolyTime.binary_mod.comp
      ((hx.comp (ComputableInPolyTime.fst _ _)).prod
        (hp.comp (ComputableInPolyTime.fst _ _)))
  have htest : ComputableInPolyTime
      (fun x : (ℕ × ℕ × ℕ) × ℕ => decide
        (Turing.MultiTapeTM.powMod x.1.1 x.1.2.1 x.2 = x.1.2.2 % x.1.1))
      (encPair encNat3 encNat) encBool :=
    ComputableInPolyTime.of_tidy
      (ComputableTidilyInPolyTime.decide_eq' hpower.tidy htarget.tidy)
  have hterm : ComputableInPolyTime
      (fun x : (ℕ × ℕ × ℕ) × ℕ =>
        if Turing.MultiTapeTM.powMod x.1.1 x.1.2.1 x.2 = x.1.2.2 % x.1.1 then x.2 else 0)
      (encPair encNat3 encNat) encNat := by
    simpa only [decide_eq_true_eq] using
      ComputableInPolyTime.ite' htest (ComputableInPolyTime.snd _ _)
        (ComputableInPolyTime.const 0)
  exact CountingFunction.sum_range (Decoder.pair Decoder.nat (Decoder.pair Decoder.nat Decoder.nat))
    (CountingFunction.of_polyTime hterm) (ComputableInPolyTime.binary_sub' hp (.const 1))

/-- At a primitive root, the computed natural sum is its target's unique bounded logarithm. -/
theorem modularLogSum_spec {p : ℕ} [Fact p.Prime] {g x : ℕ}
    (hg : IsPrimitiveRoot (g : ZMod p) (p - 1)) (hx : (x : ZMod p) ≠ 0) :
    modularLogSum p g x < p - 1 ∧ (g : ZMod p) ^ modularLogSum p g x = x := by
  rw [modularLogSum_eq_generatorLogSum (Fact.out : p.Prime).ne_zero]
  exact ZMod.generatorLogSum_spec hg hx

end Cslib.Complexity
