/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Total modular arithmetic within function levels

The existing square-and-multiply certificate charges binary exponents and intermediate residues.
Combining its three arguments through fixed tagged oracles preserves a function level. Modulus
zero has the existing fixed default, rather than an exponentially long unreduced power.
-/

public section

namespace Cslib.Complexity.CountingFunction

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ} {f g : α → ℕ}

/-- Binary natural multiplication preserves the common function level. -/
theorem nat_mul (hf : f ∈ CountingFunction a enc encNat)
    (hg : g ∈ CountingFunction a enc encNat) :
    (fun w => f w * g w) ∈ CountingFunction a enc encNat :=
  map (prod hf hg) (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.binary_mul)

/-- Binary natural remainder preserves the common function level, including the total value
`n % 0 = n`. -/
theorem nat_mod (hf : f ∈ CountingFunction a enc encNat)
    (hg : g ∈ CountingFunction a enc encNat) :
    (fun w => f w % g w) ∈ CountingFunction a enc encNat :=
  map (prod hf hg) ComputableInPolyTime.binary_mod

/-- Comparing binary naturals preserves their common function level. -/
theorem nat_lt (hf : f ∈ CountingFunction a enc encNat)
    (hg : g ∈ CountingFunction a enc encNat) :
    (fun w => decide (f w < g w)) ∈ CountingFunction a enc encBool :=
  map (prod hf hg) ComputableInPolyTime.binary_lt

/-- Binary modular exponentiation preserves the level of its three uniformly accessible inputs.
For modulus zero, `powMod` returns one. -/
theorem powMod {α : Type} {enc : α ↪ List Bool} {a : ℕ} {m x e : α → ℕ}
    (hm : m ∈ CountingFunction a enc encNat) (hx : x ∈ CountingFunction a enc encNat)
    (he : e ∈ CountingFunction a enc encNat) :
    (fun w => Turing.MultiTapeTM.powMod (m w) (x w) (e w)) ∈
      CountingFunction a enc encNat := by
  have hpower : ComputableInPolyTime
      (fun p : ℕ × (ℕ × ℕ) => Turing.MultiTapeTM.powMod p.1 p.2.1 p.2.2)
      (encPair encNat (encPair encNat encNat)) encNat :=
    computableInPolyTime_powMod (by fun_prop) (by fun_prop) (by fun_prop)
  exact map (prod hm (prod hx he)) hpower

end Cslib.Complexity.CountingFunction
