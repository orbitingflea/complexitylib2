/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
public import Cslib.Probability.PMF
public import Mathlib.Logic.Equiv.Fintype

/-!
# Running and relabelling generic group programs

`runLabeled L A` runs a program `A` with private coins against the group oracle of the labeling
`L` ([BonehShoup2023], Section 16.3, p. 693): fresh coins are uniform, and group queries are
answered by `answer L`.

`relabel j A` turns a program for labels in `S` into one for labels in `ZMod q`, through an
injection `j : ZMod q ↪ S`: it answers each query of `A` with at most one query of its own and
translates labels by `j`. Against a permutation `σ` of `ZMod q`, the relabelled program behaves as
`A` against the labeling `j ∘ σ` (`runLabeled_relabel`), and it makes no more queries than `A`
(`isQueryBounded_relabel`). Since a uniform injection `ZMod q ↪ S` is a uniform injection after a
uniform permutation (`uniform_embedding_bind_eq`), a statement about generic groups with labels in
`S` reduces to one with labels in `ZMod q` and a uniform permutation as labeling, in which no group
operation is ever rejected. This replaces the set `S′` and the resampling of the book's Game 1 in
the proof of Theorem 16.3. The names in this file are this library's.

## Main definitions

* `Cslib.Crypto.GenericGroup.runLabeled`: run a program with private coins against `answer L`.
* `Cslib.Crypto.GenericGroup.relabel`: the program for labels in `ZMod q` obtained through `j`.

## Main results

* `Cslib.Crypto.GenericGroup.runLabeled_relabel`: relabelling against `σ` is running against
  `j ∘ σ`.
* `Cslib.Crypto.GenericGroup.isQueryBounded_relabel`: relabelling preserves a query bound.
* `Cslib.Crypto.GenericGroup.uniform_embedding_bind_eq`: a uniform injective labeling is a
  uniform injective labeling after a uniform permutation of `ZMod q`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.3, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability

variable {q : ℕ} {S : Type}

/-- Run a program with private coins against the group oracle of the labeling `L`: coins are
uniform and group queries are answered by `answer L`. -/
@[expose] noncomputable def runLabeled {α : Type} (L : ZMod q → S)
    (program : ProbOracleComp (GroupOracleSpec q S) α) : PMF α :=
  OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifOracle fun query => PMF.pure (answer L query)) program

/-- Answer a query for labels in `S` with at most one query for labels in `ZMod q`, translating
labels through `j`. A group operation on a label outside the image of `j` is rejected without a
query. -/
private noncomputable def relabelHandler (j : ZMod q ↪ S) :
    (query : GroupQuery q S) →
      ProbOracleComp (GroupOracleSpec q (ZMod q)) (GroupOracleSpec q S query)
  | .label β =>
      (fun x : ZMod q => j x) <$>
        ProbOracleComp.query (spec := GroupOracleSpec q (ZMod q)) (.label β)
  | .op ℓ₁ ℓ₂ κ₁ κ₂ =>
      match Function.partialInv j ℓ₁, Function.partialInv j ℓ₂ with
      | some x₁, some x₂ =>
          (fun r : Option (ZMod q) => r.map j) <$>
            ProbOracleComp.query (spec := GroupOracleSpec q (ZMod q)) (.op x₁ x₂ κ₁ κ₂)
      | _, _ => pure none

/-- The program for labels in `ZMod q` that runs `A` and answers its queries through `j`, with at
most one query for each query of `A`. -/
noncomputable def relabel {α : Type} (j : ZMod q ↪ S)
    (A : ProbOracleComp (GroupOracleSpec q S) α) : ProbOracleComp (GroupOracleSpec q (ZMod q)) α :=
  ProbOracleComp.simulate (relabelHandler j) A

private theorem partialInv_comp_perm (j : ZMod q ↪ S) (σ : Equiv.Perm (ZMod q)) (ℓ : S) :
    Function.partialInv (fun β => j (σ β)) ℓ = (Function.partialInv j ℓ).map σ.symm := by
  have hj : Function.IsPartialInv j (Function.partialInv j) := j.injective.isPartialInv
  have hjσ : Function.IsPartialInv (fun β => j (σ β)) (Function.partialInv fun β => j (σ β)) :=
    (j.injective.comp σ.injective).isPartialInv
  cases h : Function.partialInv j ℓ with
  | some x =>
    rw [Option.map_some]
    exact (hjσ _ _).mpr (by simpa using (hj x ℓ).mp h)
  | none =>
    rw [Option.map_none]
    by_contra hne
    obtain ⟨β, hβ⟩ := Option.ne_none_iff_exists'.mp hne
    have := (hj (σ β) ℓ).mpr ((hjσ β ℓ).mp hβ)
    simp [h] at this

/-- Against a permutation `σ` of `ZMod q`, the relabelled program has the law of `A` against the
labeling `j ∘ σ`. -/
theorem runLabeled_relabel {α : Type} (j : ZMod q ↪ S) (σ : Equiv.Perm (ZMod q))
    (A : ProbOracleComp (GroupOracleSpec q S) α) :
    runLabeled (σ : ZMod q → ZMod q) (relabel j A) = runLabeled (fun β => j (σ β)) A := by
  unfold runLabeled relabel
  rw [ProbOracleComp.interpret_simulate]
  congr 2
  funext query
  cases query with
  | label β => simp [relabelHandler]
  | op ℓ₁ ℓ₂ κ₁ κ₂ =>
    have h₁ := partialInv_comp_perm j σ ℓ₁
    have h₂ := partialInv_comp_perm j σ ℓ₂
    have hσ : ∀ x, Function.partialInv (σ : ZMod q → ZMod q) x = some (σ.symm x) := fun x =>
      (σ.injective.isPartialInv _ _).mpr (by simp)
    simp only [relabelHandler, answer_op, h₁, h₂]
    cases Function.partialInv j ℓ₁ <;> cases Function.partialInv j ℓ₂ <;>
      simp [answer_op, hσ]

/-- Relabelling makes at most as many queries as the program: this is the query-count certificate
of the reduction. -/
theorem isQueryBounded_relabel {α : Type} (j : ZMod q ↪ S)
    {A : ProbOracleComp (GroupOracleSpec q S) α} {T : ℕ} (hA : A.IsQueryBounded T) :
    (relabel j A).IsQueryBounded T := by
  refine ProbOracleComp.IsQueryBounded.simulate (fun query => ?_) hA
  cases query with
  | label β =>
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.isCostBounded_query _ _)
  | op ℓ₁ ℓ₂ κ₁ κ₂ =>
    simp only [relabelHandler]
    split
    · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ProbOracleComp.isCostBounded_query _ _)
    · exact .pure _ _

/-- A uniform injective labeling is a uniform injective labeling after a uniform permutation of
`ZMod q`. -/
theorem uniform_embedding_bind_eq [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)] {β : Type}
    (f : (ZMod q ↪ S) → PMF β) :
    (PMF.uniformOfFintype (ZMod q ↪ S)).bind f =
      (PMF.uniformOfFintype (ZMod q ↪ S)).bind fun j =>
        (PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind fun σ => f (σ.toEmbedding.trans j) := by
  have key : ∀ σ : Equiv.Perm (ZMod q),
      (PMF.uniformOfFintype (ZMod q ↪ S)).bind (fun j => f (σ.toEmbedding.trans j)) =
        (PMF.uniformOfFintype (ZMod q ↪ S)).bind f := by
    intro σ
    let e : (ZMod q ↪ S) ≃ (ZMod q ↪ S) :=
      { toFun := fun j => σ.toEmbedding.trans j
        invFun := fun j => σ.symm.toEmbedding.trans j
        left_inv := fun j => by ext x; simp
        right_inv := fun j => by ext x; simp }
    conv_rhs => rw [← PMF.uniformOfFintype_map_equiv e]
    rw [PMF.bind_map]
    rfl
  rw [PMF.bind_comm]
  simp_rw [key]
  rw [PMF.bind_const]

end Cslib.Crypto.GenericGroup
