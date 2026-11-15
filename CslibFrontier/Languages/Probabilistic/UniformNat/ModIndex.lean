/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat

/-!
# Residue samples capped at the modulus

`sampleModIndex width bound` draws `sampleModNat width bound` and caps the result at `bound`. For
`0 < bound` every residue is already below `bound`, so the cap changes nothing
(`sampleModIndex_eq_sampleModNat`); for `bound = 0` the sampler returns `0`. The cap keeps the
unary encoding of the output polynomially bounded for every `bound`; its certificate is
`Cslib.Probability.isPPTOn_sampleModIndex` in
`CslibFrontier/Computability/Probabilistic/UniformNat/ModIndex.lean`.

## Main definitions

* `Cslib.ProbComp.sampleModIndex`: `sampleModNat` capped at the modulus.

## Main results

* `Cslib.ProbComp.sampleModIndex_eq_sampleModNat`: for a positive modulus the cap changes nothing.
-/

public section

namespace Cslib.ProbComp

/-- Sample a modular residue via `ProbComp.sampleModNat width bound`, capped at `bound` so its
unary encoding is polynomially bounded even when `bound = 0`. When `0 < bound`, every residue modulo
`bound` is strictly below `bound`, so `sampleModIndex width bound = sampleModNat width bound`. -/
@[expose] noncomputable def sampleModIndex (width bound : ℕ) : ProbComp ℕ :=
  min bound <$> sampleModNat width bound

/-- When `0 < bound`, `sampleModIndex width bound` equals `sampleModNat width bound`. -/
@[simp] theorem sampleModIndex_eq_sampleModNat (width : ℕ) {bound : ℕ} (hbound : 0 < bound) :
    sampleModIndex width bound = sampleModNat width bound := by
  simp only [sampleModIndex, sampleModNat, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_def]
  congr 1; funext x
  rw [Nat.min_eq_right (Nat.mod_lt x hbound).le]

end Cslib.ProbComp
