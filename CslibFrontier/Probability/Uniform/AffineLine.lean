/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.SelfCorrection
public import CslibFrontier.Languages.Probabilistic.Semantics
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Uniformity along an affine line in a finite vector space

Over a finite vector space `V` over a field `F`, the affine map `v ↦ x + c • v` (`c ≠ 0`) is a
bijection (`Cslib.Code.affineLineEquiv`), so pushing the uniform distribution on `V` forward along
`v ↦ x + c • v` preserves uniformity. This is kept in a leaf module so algebraic self-correction
modules (`CslibFrontier.Foundations.Data.Code.SelfCorrection`) do not depend on `PMF` or `ProbComp`.

## Main results

* `Cslib.Probability.PMF.map_add_smul_uniformOfFintype`:
  `(PMF.uniformOfFintype V).map (fun v => x + c • v) = PMF.uniformOfFintype V` for `c ≠ 0`.
* `Cslib.ProbComp.eval_map_add_smul_uniform`: sampling `v` uniformly from `V` and returning
  `x + c • v` (`c ≠ 0`) has the uniform law on `V`.
-/

public section

namespace Cslib.Probability.PMF

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [Fintype V] [Nonempty V]

/-- If `v` is uniformly distributed on a finite vector space `V` over `F` and `c ≠ 0`, then
`x + c • v` is uniformly distributed on `V`. -/
theorem map_add_smul_uniformOfFintype (x : V) {c : F} (hc : c ≠ 0) :
    (PMF.uniformOfFintype V).map (fun v => x + c • v) = PMF.uniformOfFintype V :=
  uniformOfFintype_map_equiv (Cslib.Code.affineLineEquiv x hc)

end Cslib.Probability.PMF

namespace Cslib.ProbComp

open Cslib.Probability

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] [Fintype V] [Nonempty V]

/-- Sampling `v` uniformly from `V` and returning `x + c • v` for `c ≠ 0` has the uniform law on
`V`. -/
theorem eval_map_add_smul_uniform (x : V) {c : F} (hc : c ≠ 0) :
    ProbComp.eval ((fun v => x + c • v) <$> ProbComp.uniform V) = PMF.uniformOfFintype V := by
  rw [ProbComp.eval_map, ProbComp.eval_uniform,
    Cslib.Probability.PMF.map_add_smul_uniformOfFintype x hc]

end Cslib.ProbComp
