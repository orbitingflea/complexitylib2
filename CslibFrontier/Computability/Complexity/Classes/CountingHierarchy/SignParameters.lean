/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.ResidueAccess
public import CslibFrontier.Foundations.NumberTheory.PrimeWindowSign
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Preparing short parameters for residue signs

The manuscript parameters are ordinary polynomial-time arithmetic on binary magnitude and
excluded-prime bounds. The precision is output in unary because it counts actual bits of the
dyadic scale. The cutoff and doubling limit are output in binary and may have exponential value.
Neither the represented integer nor the prime product is computed.
-/

public section

namespace Cslib.PrimeWindowSign

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {m L : α → ℕ}

/-- The exact prime cutoff has a polynomial-time binary certificate. -/
theorem cutoff_polyTime (hm : ComputableInPolyTime m enc encNat)
    (hL : ComputableInPolyTime L enc encNat) :
    ComputableInPolyTime (fun w => cutoff (m w) (L w)) enc encNat := by
  have hZ := ComputableInPolyTime.binary_max' (ComputableInPolyTime.const 16)
    (ComputableInPolyTime.binary_max' hm hL)
  exact ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.binary_pow' hZ (ComputableInPolyTime.const 4))

/-- The dyadic precision counts polynomially many bits, so it is computable in unary. -/
theorem precision_polyTime (hm : ComputableInPolyTime m enc encNat)
    (hL : ComputableInPolyTime L enc encNat) :
    ComputableInPolyTime (fun w => (cutoff (m w) (L w)).size + 10) enc encUnary :=
  ComputableInPolyTime.unary_add'
    (ComputableInPolyTime.binary_size.comp (cutoff_polyTime hm hL))
    (ComputableInPolyTime.const 10)

/-- The doubling limit has polynomial binary length even when exponentially large. -/
theorem doublingLimit_polyTime (hm : ComputableInPolyTime m enc encNat)
    (hL : ComputableInPolyTime L enc encNat) :
    ComputableInPolyTime (fun w =>
      cutoff (m w) (L w) * (cutoff (m w) (L w)).size + 1) enc encNat := by
  have hY := cutoff_polyTime hm hL
  have hsize := ComputableInPolyTime.unary_to_binary.comp
    (ComputableInPolyTime.binary_size.comp hY)
  exact ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_mul' hY hsize)
    (ComputableInPolyTime.const 1)

end Cslib.PrimeWindowSign
