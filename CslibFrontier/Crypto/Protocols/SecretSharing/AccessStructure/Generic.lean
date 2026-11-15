/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.SecretSharing.AccessStructure.Basic
import CslibFrontier.Languages.Probabilistic.Sharing
import CslibFrontier.Probability.Uniform

/-!
# Generic Secret-Sharing Construction for Monotone Access Structures

This module formalizes Construction 22.1 of [BonehShoup2023], Section 22.5.1 (pp. 976–977): the
generic secret-sharing scheme implementing any monotone access structure `A : AccessStructure Party`
on a finite party type `Party` (`[Fintype Party] [DecidableEq Party] [DecidablePred A.authorized]`)
with `¬ A.authorized ∅` over an additive commutative group `G` (`[AddCommGroup G]`):

- `AccessStructure.authorizedSets`: the finite set of all authorized coalitions `J ⊆ Party`.
- `AccessStructure.authorizedContaining`: for each party `i`, the finite set
  `A^(i) = {J ∈ A : i ∈ J}` of authorized coalitions containing `i`.
- `GenericKey A G`: for each `J ∈ A.authorizedSets`, `J.card - 1` random pads in `G`.
- `GenericShare A G i`: one element of `G` for each `J ∈ A.authorizedContaining i` (so `|A^(i)|`
  elements of `G` in total).
- `genericShare`: for each authorized coalition `J ∈ A^(i)`, party `i` receives its coordinate of
  the `|J|`-out-of-`|J|` additive sharing `Cslib.ProbComp.completeShares J.card secret (r J)`.
- `genericReconstruct`: for an authorized coalition `s`, sums the `s`-coordinate of each member
  `j ∈ s`'s share (`∑ j : s, v j ⟨s, _⟩`), returning `0` on unauthorized coalitions.
- `genericAccessScheme`: packages `genericShare` and `genericReconstruct` over translation-invariant
  key distributions `genericSources A G`. For finite `G`, `genericSources A G = {uniformOfFintype}`;
  for infinite `G`, `genericSources A G = ∅` once some authorized coalition has two members, so
  privacy is vacuous and only correctness holds nontrivially.
- `genericUniformAccessScheme` and `genericUniform_viewDist_eq`: canonical finite-group instance
  with uniform pads, under which every unauthorized coalition's view distribution is uniform on
  `(i : s) → GenericShare A G i.1` and independent of the secret.

Differences from [BonehShoup2023], Section 22.5.1:
1. The hypothesis `hempty : ¬ A.authorized ∅` is explicit (Definition 22.18 allows `∅ ∈ A`, for
   which Construction 22.1's empty sum returns `0` and no scheme over a nontrivial secret space can
   be correct; see `not_perfectlyCorrect_of_authorized_empty` in
   `CslibFrontier/Crypto/Protocols/SecretSharing/AccessStructure/Recognition.lean`).
2. Secrets lie in any `AddCommGroup G` rather than only `ZMod q`, and parties form any finite type
   `Party` with decidable equality rather than `{1, …, N}`.
3. Following Construction 22.1 literally, one independent additive sharing is generated for every
   authorized coalition `J ∈ A.authorizedSets`, so `(genericAccessScheme A G hempty).access = A` is
   `rfl` and `genericReconstruct` sums the `s`-coordinate directly without choosing a minimal
   authorized subset (the minimal-set scheme of Example 22.1, which shares only over `{1, 2, 3}`
   and `{1, 3, 4}`, is not formalized).

## Main definitions

* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.authorizedSets`: finite set of all
  authorized coalitions of `A`.
* `Cslib.Crypto.Protocols.SecretSharing.AccessStructure.authorizedContaining`: finite set
  `A^(i) = {J ∈ A : i ∈ J}` of authorized coalitions containing party `i`.
* `Cslib.Crypto.Protocols.SecretSharing.GenericKey`,
  `Cslib.Crypto.Protocols.SecretSharing.GenericShare`: key and party-indexed share types for
  Construction 22.1.
* `Cslib.Crypto.Protocols.SecretSharing.genericShare`,
  `Cslib.Crypto.Protocols.SecretSharing.genericReconstruct`: sharing and reconstruction maps of
  Construction 22.1.
* `Cslib.Crypto.Protocols.SecretSharing.genericSources`,
  `Cslib.Crypto.Protocols.SecretSharing.genericAccessScheme`,
  `Cslib.Crypto.Protocols.SecretSharing.genericUniformAccessScheme`: translation-invariant and
  uniform `AccessScheme` instances for Construction 22.1.

## Main results

* `Cslib.Crypto.Protocols.SecretSharing.genericReconstruct_genericShare`: universal correctness of
  Construction 22.1 on every authorized coalition when `¬ A.authorized ∅`.
* `Cslib.Crypto.Protocols.SecretSharing.genericUniform_viewDist_eq`: under uniform key pads, every
  unauthorized coalition's view distribution is uniform on `(i : s) → GenericShare A G i.1`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Version 0.6,
  Section 22.5.1, Construction 22.1 and Example 22.1, pp. 976–977.
-/

public section

namespace Cslib.Crypto.Protocols.SecretSharing

open Cslib.Probability Cslib.Probability.PMF

namespace AccessStructure

variable {Party : Type*} [Fintype Party]

/-- The finite set of all authorized coalitions of `A`. -/
@[expose] def authorizedSets (A : AccessStructure Party) [DecidablePred A.authorized] :
    Finset (Finset Party) :=
  Finset.univ.filter A.authorized

@[simp]
theorem mem_authorizedSets (A : AccessStructure Party) [DecidablePred A.authorized]
    (J : Finset Party) :
    J ∈ A.authorizedSets ↔ A.authorized J := by
  simp [authorizedSets]

/-- The set `A^(i) = {J ∈ A : i ∈ J}` of all authorized coalitions of `A` containing party `i`
([BonehShoup2023], Construction 22.1, p. 977). -/
@[expose] def authorizedContaining (A : AccessStructure Party) [DecidableEq Party]
    [DecidablePred A.authorized] (i : Party) : Finset (Finset Party) :=
  A.authorizedSets.filter (i ∈ ·)

@[simp]
theorem mem_authorizedContaining (A : AccessStructure Party) [DecidableEq Party]
    [DecidablePred A.authorized] (i : Party) (J : Finset Party) :
    J ∈ A.authorizedContaining i ↔ A.authorized J ∧ i ∈ J := by
  simp [authorizedContaining]

instance [DecidableEq Party] (B : Finset (Finset Party)) (s : Finset Party) :
    Decidable ((ofSets (B : Set (Finset Party))).authorized s) :=
  decidable_of_iff (∃ b ∈ B, b ⊆ s) (by simp)

end AccessStructure

section GenericConstruction

variable {Party : Type*} [Fintype Party] [DecidableEq Party]

/-- Randomness (key) type for Construction 22.1 ([BonehShoup2023], p. 977): for each authorized
coalition `J ∈ A.authorizedSets`, `J.card - 1` random pads in `G`. -/
abbrev GenericKey (A : AccessStructure Party) [DecidablePred A.authorized] (G : Type*) : Type _ :=
  (J : A.authorizedSets) → Fin (J.1.card - 1) → G

/-- Share type for party `i` in Construction 22.1 ([BonehShoup2023], p. 977): one element of `G`
for each authorized coalition `J ∈ A^(i) = A.authorizedContaining i` (so `|A^(i)|` elements of `G`
in total). -/
abbrev GenericShare (A : AccessStructure Party) [DecidablePred A.authorized]
    (G : Type*) (i : Party) : Type _ :=
  (J : A.authorizedContaining i) → G

/-- Sharing map `G(α)` of Construction 22.1 ([BonehShoup2023], p. 977): for each authorized
coalition `J ∈ A^(i)`, party `i` receives its coordinate of the `|J|`-out-of-`|J|` additive
sharing `ProbComp.completeShares J.card secret (r J)`. -/
noncomputable def genericShare (A : AccessStructure Party) [DecidablePred A.authorized]
    {G : Type*} [AddCommGroup G] (r : GenericKey A G) (secret : G) (i : Party) :
    GenericShare A G i :=
  fun J =>
    have hJ : A.authorized J.1 ∧ i ∈ J.1 := (A.mem_authorizedContaining i J.1).mp J.2
    Cslib.ProbComp.completeShares J.1.card secret
      (r ⟨J.1, (A.mem_authorizedSets J.1).mpr hJ.1⟩)
      (J.1.equivFin ⟨i, hJ.2⟩)

/-- Sharing in Construction 22.1 is additively homomorphic in the key and secret. -/
theorem genericShare_add (A : AccessStructure Party) [DecidablePred A.authorized]
    {G : Type*} [AddCommGroup G] (r₁ r₂ : GenericKey A G) (secret₁ secret₂ : G) (i : Party) :
    genericShare A (r₁ + r₂) (secret₁ + secret₂) i =
      genericShare A r₁ secret₁ i + genericShare A r₂ secret₂ i := by
  ext J
  simp only [genericShare, Pi.add_apply]
  exact congrFun (Cslib.ProbComp.completeShares_add J.1.card secret₁ secret₂ _ _) _

/-- Reconstruction map `C(J, {α_j}_{j ∈ J})` of Construction 22.1 ([BonehShoup2023], p. 977):
when `s` is authorized, sum the `s`-coordinate of each member `j ∈ s`'s share; otherwise return
`0`. -/
@[expose] def genericReconstruct (A : AccessStructure Party) [DecidablePred A.authorized]
    {G : Type*} [AddCommGroup G] (s : Finset Party) (v : (j : s) → GenericShare A G j.1) : G :=
  if hs : A.authorized s then
    ∑ j : s, v j ⟨s, (A.mem_authorizedContaining j.1 s).mpr ⟨hs, j.2⟩⟩
  else
    0

/-- Correctness of Construction 22.1: when `¬ A.authorized ∅`, every authorized coalition `s`
reconstructs `secret` for every key `r`. -/
theorem genericReconstruct_genericShare (A : AccessStructure Party) [DecidablePred A.authorized]
    {G : Type*} [AddCommGroup G] (hempty : ¬ A.authorized ∅) (r : GenericKey A G) (secret : G)
    {s : Finset Party} (hs : A.authorized s) :
    genericReconstruct A s (fun j => genericShare A r secret j.1) = secret := by
  have hne : s.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    exact hempty hs
  have : NeZero s.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr hne)⟩
  simp only [genericReconstruct, hs, ↓reduceDIte, genericShare]
  have hsum := Equiv.sum_comp (s.equivFin)
    (Cslib.ProbComp.completeShares s.card secret (r ⟨s, (A.mem_authorizedSets s).mpr hs⟩))
  rw [hsum, Cslib.ProbComp.sum_completeShares]

/-- The class of translation-invariant key distributions on `GenericKey A G`. For finite `G`,
`genericSources A G = {uniformOfFintype}`. For infinite `G`, `genericSources A G = ∅` once some
authorized coalition has two members. -/
@[expose] def genericSources (A : AccessStructure Party) [DecidablePred A.authorized]
    (G : Type*) [AddCommGroup G] : SourceClass (GenericKey A G) :=
  { P | ∀ δ : GenericKey A G, P.map (· + δ) = P }

/-- The uniform distribution on `GenericKey A G` is translation-invariant. -/
theorem uniformOfFintype_mem_genericSources (A : AccessStructure Party)
    [DecidablePred A.authorized] (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G] :
    uniformOfFintype (GenericKey A G) ∈ genericSources A G := fun δ =>
  uniformOfFintype_map_add_right δ

/-- For any unauthorized coalition `s`, any secrets `m₀, m₁`, and any desired view offset `c`,
there exists a key shift `δ : GenericKey A G` translating the coalition view of `m₀` by `c` into
the coalition view of `m₁`. -/
private theorem exists_genericKey_shift (A : AccessStructure Party) [DecidablePred A.authorized]
    {G : Type*} [AddCommGroup G] {s : Finset Party} (hs : ¬ A.authorized s)
    (m₀ m₁ : G) (c : (i : s) → GenericShare A G i.1) :
    ∃ δ : GenericKey A G, ∀ r : GenericKey A G,
      (fun i : s => genericShare A (r + δ) m₁ i.1) =
        (fun i : s => genericShare A r m₀ i.1) + c := by
  classical
  have hex : ∀ J : A.authorizedSets, ∃ p₀ ∈ J.1, p₀ ∉ s := by
    intro J
    by_contra! hsub
    exact hs (A.mono hsub ((A.mem_authorizedSets J.1).mp J.2))
  choose p₀ hp₀J hp₀s using hex
  let base (J : A.authorizedSets) (k : Fin J.1.card) : G :=
    let p : J.1 := (J.1.equivFin).symm k
    if hp : p.1 ∈ s then
      c ⟨p.1, hp⟩ ⟨J.1, (A.mem_authorizedContaining p.1 J.1).mpr
        ⟨(A.mem_authorizedSets J.1).mp J.2, p.2⟩⟩
    else 0
  let δ : GenericKey A G := fun J =>
    Cslib.ProbComp.initOfShares J.1.card
      (Function.update (base J) (J.1.equivFin ⟨p₀ J, hp₀J J⟩)
        (m₁ - m₀ - ∑ k ∈ Finset.univ.erase (J.1.equivFin ⟨p₀ J, hp₀J J⟩), base J k))
  refine ⟨δ, fun r => ?_⟩
  ext ⟨i, hi⟩ ⟨J, hJ⟩
  have hJ_auth : A.authorized J ∧ i ∈ J := (A.mem_authorizedContaining i J).mp hJ
  let J' : A.authorizedSets := ⟨J, (A.mem_authorizedSets J).mpr hJ_auth.1⟩
  have : NeZero J.card := ⟨Nat.ne_of_gt (Finset.card_pos.mpr ⟨i, hJ_auth.2⟩)⟩
  change
    Cslib.ProbComp.completeShares J.card m₁ (r J' + δ J') (J.equivFin ⟨i, hJ_auth.2⟩) =
      Cslib.ProbComp.completeShares J.card m₀ (r J') (J.equivFin ⟨i, hJ_auth.2⟩) +
        c ⟨i, hi⟩ ⟨J, hJ⟩
  have hm₁ : m₁ = m₀ + (m₁ - m₀) := (add_sub_cancel m₀ m₁).symm
  rw [hm₁, Cslib.ProbComp.completeShares_add]
  simp only [Pi.add_apply]
  congr 1
  have hcomp : Cslib.ProbComp.completeShares J.card (m₁ - m₀) (δ J') =
      Function.update (base J') (J.equivFin ⟨p₀ J', hp₀J J'⟩)
        (m₁ - m₀ - ∑ k ∈ Finset.univ.erase (J.equivFin ⟨p₀ J', hp₀J J'⟩), base J' k) :=
    Cslib.ProbComp.completeShares_initOfShares J.card (by
      rw [Finset.sum_update_of_mem (Finset.mem_univ _), Finset.sdiff_singleton_eq_erase,
        sub_add_cancel])
  rw [congrFun hcomp (J.equivFin ⟨i, hJ_auth.2⟩)]
  have hne : J.equivFin ⟨i, hJ_auth.2⟩ ≠ J.equivFin ⟨p₀ J', hp₀J J'⟩ := by
    intro heq
    have hval : i = p₀ J' := congrArg Subtype.val (J.equivFin.injective heq)
    exact hp₀s J' (hval ▸ hi)
  rw [Function.update_of_ne hne]
  dsimp [base, J']
  rw [Equiv.symm_apply_apply]
  simp [hi]

private theorem genericView_eq_of_not_authorized (A : AccessStructure Party)
    [DecidablePred A.authorized] {G : Type*} [AddCommGroup G]
    {P : PMF (GenericKey A G)} (hP : P ∈ genericSources A G)
    {s : Finset Party} (hs : ¬ A.authorized s) (m₀ m₁ : G) :
    AccessStructure.viewDistOf P (genericShare A) s m₀ =
      AccessStructure.viewDistOf P (genericShare A) s m₁ := by
  obtain ⟨δ, hδ⟩ := exists_genericKey_shift A hs m₀ m₁ 0
  have hcongr :
      AccessStructure.viewDistOf P (genericShare A) s m₀ =
        AccessStructure.viewDistOf (P.map (· + δ)) (genericShare A) s m₁ := by
    simp only [AccessStructure.viewDistOf, PMF.map_comp]
    congr 1
    funext r
    have hr := hδ r
    rw [add_zero] at hr
    exact hr.symm
  rw [hcongr, hP δ]

/-- **Construction 22.1** ([BonehShoup2023], Section 22.5.1, p. 977): the generic secret-sharing
scheme over `genericSources A G` implementing any monotone access structure `A` with
`¬ A.authorized ∅`. For finite `G`, `genericSources A G = {uniformOfFintype}`. For infinite `G`,
`genericSources A G = ∅` once some authorized coalition has two members, so privacy is vacuous
(only correctness holds nontrivially); use `genericUniformAccessScheme` for finite groups. -/
@[expose] noncomputable def genericAccessScheme (A : AccessStructure Party)
    [DecidablePred A.authorized] (G : Type*) [AddCommGroup G] (hempty : ¬ A.authorized ∅) :
    AccessScheme G (GenericKey A G) Party (GenericShare A G) where
  access := A
  sources := genericSources A G
  share := genericShare A
  reconstruct := genericReconstruct A
  correct r secret _ hs := by exact genericReconstruct_genericShare A hempty r secret hs
  view_indist _ hP _ hs := by exact genericView_eq_of_not_authorized A hP hs

@[simp]
theorem genericAccessScheme_access (A : AccessStructure Party) [DecidablePred A.authorized]
    (G : Type*) [AddCommGroup G] (hempty : ¬ A.authorized ∅) :
    (genericAccessScheme A G hempty).access = A :=
  rfl

/-- Canonical finite-group instance of Construction 22.1 with uniform key pads. -/
@[expose] noncomputable def genericUniformAccessScheme (A : AccessStructure Party)
    [DecidablePred A.authorized] (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G]
    (hempty : ¬ A.authorized ∅) :
    AccessScheme G (GenericKey A G) Party (GenericShare A G) :=
  (genericAccessScheme A G hempty).monoSources
    (Set.singleton_subset_iff.mpr (uniformOfFintype_mem_genericSources A G))

@[simp]
theorem genericUniformAccessScheme_access (A : AccessStructure Party) [DecidablePred A.authorized]
    (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G] (hempty : ¬ A.authorized ∅) :
    (genericUniformAccessScheme A G hempty).access = A :=
  rfl

/-- Under uniform key pads, every unauthorized coalition's view distribution in Construction 22.1
is uniform on `(i : s) → GenericShare A G i.1` and independent of `secret`. -/
theorem genericUniform_viewDist_eq (A : AccessStructure Party) [DecidablePred A.authorized]
    (G : Type*) [AddCommGroup G] [Fintype G] [Nonempty G] (hempty : ¬ A.authorized ∅)
    {s : Finset Party} (hs : ¬ A.authorized s) (secret : G) :
    (genericUniformAccessScheme A G hempty).viewDist
        (uniformOfFintype (GenericKey A G)) s secret =
      uniformOfFintype ((i : s) → GenericShare A G i.1) := by
  apply Cslib.Probability.PMF.uniformOfFintype_map_of_shift
  intro c
  obtain ⟨δ, hδ⟩ := exists_genericKey_shift A hs secret secret c
  refine ⟨Equiv.addRight δ, fun r => ?_⟩
  exact hδ r

end GenericConstruction

end Cslib.Crypto.Protocols.SecretSharing
