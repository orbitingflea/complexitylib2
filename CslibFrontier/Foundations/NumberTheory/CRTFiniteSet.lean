/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.CRTCircle

/-!
# Cofactors indexed by a finite set

The cofactor of an indexed family on a finset subtype is exactly the product over that
finset with the distinguished index erased. This is `Finset.prod_erase_attach` in the
`crtCofactor` API and requires no positivity or nonzero hypotheses.

## Main results

* `Cslib.crtCofactor_finset`: the subtype cofactor as an erased-finset product.
-/

public section

namespace Cslib

/-- Replace the subtype-indexed CRT cofactor by the corresponding erased-finset product. -/
theorem crtCofactor_finset {α : Type*} [DecidableEq α] (s : Finset α)
    (f : α → ℤ) (p : s) :
    crtCofactor (fun q : s => f q.val) p = ∏ q ∈ s.erase p.val, f q := by
  unfold crtCofactor
  rw [Finset.univ_eq_attach]
  exact Finset.prod_erase_attach f p

end Cslib
