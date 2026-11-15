/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Probability/PMF.lean`)

public import CslibFrontier.Probability.PMF.Uniform
public import Mathlib.Data.Fintype.Perm

/-!
# Precomposing a uniform embedding with a uniform permutation of its domain

Precomposing a uniformly chosen embedding `T ↪ α` with an independent uniform permutation
`σ : Equiv.Perm T` of its domain leaves the distribution of a two-stage experiment unchanged
(`uniformOfFintype_embedding_bind_perm_trans`).

## Main results

* `Cslib.Probability.PMF.uniformOfFintype_embedding_bind_perm_trans`: binding a uniform embedding
  `T ↪ α` equals binding after precomposing with an independent uniform permutation of `T`.
-/

public section

namespace Cslib.Probability.PMF

/-- Binding a uniform embedding `T ↪ α` equals binding after precomposing with an independent
uniform permutation of `T`. -/
theorem uniformOfFintype_embedding_bind_perm_trans {T α β : Type*} [Fintype (T ↪ α)]
    [Nonempty (T ↪ α)] [Fintype (Equiv.Perm T)] (f : (T ↪ α) → PMF β) :
    (PMF.uniformOfFintype (T ↪ α)).bind f =
      (PMF.uniformOfFintype (T ↪ α)).bind fun j =>
        (PMF.uniformOfFintype (Equiv.Perm T)).bind fun σ => f (σ.toEmbedding.trans j) := by
  rw [PMF.bind_comm]
  have key (σ : Equiv.Perm T) :
      (PMF.uniformOfFintype (T ↪ α)).bind (fun j => f (σ.toEmbedding.trans j)) =
        (PMF.uniformOfFintype (T ↪ α)).bind f :=
    uniformOfFintype_bind_equiv (σ.symm.embeddingCongr (Equiv.refl α)) f
  simp_rw [key]
  rw [PMF.bind_const]

end Cslib.Probability.PMF
