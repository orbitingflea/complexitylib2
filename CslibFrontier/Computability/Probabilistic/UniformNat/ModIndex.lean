/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PPT

/-!
# Sampling capped residues in strict polynomial time

The certificate for `Cslib.ProbComp.sampleModIndex`: with a unary bit width and a unary modulus, it
is uniformly strict PPT with unary output. It composes `isPPTOn_sampleModNat` with the cap.

## Main results

* `Cslib.Probability.isPPTOn_sampleModIndex`: the capped residue sampler is uniformly strict PPT.
-/

public section

namespace Cslib.Probability

open ProbComp Turing.MultiTapeTM

/-- Sampling a modular index with unary bit width and unary modulus is uniformly strict PPT with
unary output. -/
@[program_certificate]
theorem isPPTOn_sampleModIndex {α : Type} {input : α ↪ List Bool}
    {width bound : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hbound : ComputableInPolyTime bound input encUnary) :
    IsPPTOn input encUnary (fun a => sampleModIndex (width a) (bound a)) := by
  have hmod := isPPTOn_sampleModNat hwidth (ComputableInPolyTime.unary_to_binary.comp hbound)
  have hmin : ComputableInPolyTime (fun p : α × ℕ => min (bound p.1) p.2)
      (encPair input encNat) encUnary :=
    ComputableInPolyTime.binary_min_unary'
      (hbound.comp (ComputableInPolyTime.fst input encNat))
      (ComputableInPolyTime.snd input encNat)
  exact hmod.map_with hmin

end Cslib.Probability
