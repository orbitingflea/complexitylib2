/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Probability.ProbabilityMassFunction.Basic
public import Mathlib.Basic.ENNReal.Basic

/-!
# Expected-amortized composition with distribution invariants

`expectedAmortizedSequence` telescopes a potential over distributions while retaining a native
execution relation. The invariant is indexed by the remaining operations: it can include
admissibility, conditional seed laws, representation and trajectory-relative peak bounds.
The step supplies native execution composition rather than identifying different machine models.
In particular, the state type may retain a seed, returned observations or a transcript.
-/

public section

namespace Cslib.DataStructure

open scoped ENNReal

/-- Telescope expected potential along a list of operations, retaining native execution evidence.
`inv ops ν` contains the model's distribution obligations for the remaining operations.
`advance` returns the next distribution, its invariant, the one-step amortized inequality and
an extension of any native execution of the tail. No independence, unconditional seed law or
finite expectation is required; the proof uses addition, never subtraction of potentials. -/
theorem expectedAmortizedSequence {α Op : Type*}
    (potential : PMF α → ℝ≥0∞)
    (inv : List Op → PMF α → Prop)
    (exec : List Op → PMF α → PMF α → ℝ≥0∞ → ℝ≥0∞ → Prop)
    (empty : ∀ ν, exec [] ν ν 0 0)
    (advance : ∀ o ops ν, inv (o :: ops) ν →
      ∃ ν₁ T C, inv ops ν₁ ∧ T + potential ν₁ ≤ C + potential ν ∧
        ∀ νf Tr Cr, exec ops ν₁ νf Tr Cr → exec (o :: ops) ν νf (T + Tr) (C + Cr))
    (ops : List Op) (ν : PMF α) (hi : inv ops ν) :
    ∃ νf T C, exec ops ν νf T C ∧ inv [] νf ∧
      T + potential νf ≤ C + potential ν := by
  induction ops generalizing ν with
  | nil => exact ⟨ν, 0, 0, empty ν, hi, by simp⟩
  | cons o ops ih =>
    obtain ⟨ν₁, T, C, hi₁, hstep, extend⟩ := advance o ops ν hi
    obtain ⟨νf, Tr, Cr, hr, hif, hrest⟩ := ih ν₁ hi₁
    refine ⟨νf, T + Tr, C + Cr, extend νf Tr Cr hr, hif, ?_⟩
    calc
      (T + Tr) + potential νf = T + (Tr + potential νf) := by ac_rfl
      _ ≤ T + (Cr + potential ν₁) := add_le_add le_rfl hrest
      _ = Cr + (T + potential ν₁) := by ac_rfl
      _ ≤ Cr + (C + potential ν) := add_le_add le_rfl hstep
      _ = (C + Cr) + potential ν := by ac_rfl

end Cslib.DataStructure
