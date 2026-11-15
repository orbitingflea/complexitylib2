/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.GenericGroup.Relabel
public import CslibFrontier.Crypto.Game
import CslibFrontier.Foundations.Data.List.SortedAssoc
import CslibFrontier.Languages.Probabilistic.Oracle.CoinFixing
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.RandomPermutation
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.EmbeddingPerm
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.PMF.UniformSubset
import CslibFrontier.Probability.Product
import Mathlib.Algebra.Field.ZMod

/-!
# Discrete logarithm in the generic group model

The discrete-logarithm game in the generic group model of [BonehShoup2023], Section 16.3, and the
bound of Theorem 16.3 (p. 693): for prime `q`, an adversary that makes at most `T` queries to the
group oracle outputs the discrete logarithm with probability at most `((3T + 2)² / 2 + 1) / q`.

`dlogGame A` draws a uniform injective labeling `L : ZMod q ↪ S` and a uniform `α : ZMod q`, gives
the adversary `L 1` and `L α`, runs it against the group oracle of `L` (`runLabeled`) and wins when
it outputs `α`. The adversary's budget is `ProbOracleComp.IsQueryBounded`: at most `T` labeling and
group-operation queries on every path, whatever its private coins; coin draws are free.

This is a query bound on query-bounded programs in an idealized model; it assumes no computational
hardness and is not a statement about any specific group: as the book says (p. 695), the bound
says nothing about the difficulty of discrete logarithm in any specific group. It applies to
adversaries that are otherwise unbounded.

As in the book, `q` is prime; the bound is not claimed for composite `q`. For groups of
prime-power order the book reduces discrete logarithm to the prime case (Section 16.1.2, p. 684).
The proof uses primality only in the fact that two distinct linear forms `c X + d` agree at no more
than one point of `ZMod q`.

It differs from the book's setting as follows.

1. `S` is any finite type, not a set of bit strings; `Nonempty (ZMod q ↪ S)` is the book's
   `|S| ≥ q`.
2. The adversary may use private coins; the book's adversary is a computationally unbounded
   algorithm, and nothing beyond the query bound is assumed here either.
3. The challenger does not make labeling queries; it reads `L 1` and `L α` directly, which gives
   the same distribution.
4. Groups are additive: the label of `β` stands for `β • g`, the book's `g^β`.

The proof follows the book's (Games 0–2): reduce to labels in `ZMod q` with a uniform permutation
as labeling (`Cslib.Crypto.GenericGroup.relabel`), sample the permutation lazily, and replace it by
a table on linear forms that is identical until two distinct forms agree at `α`. The sharp form
`succProbability_dlogGame_le_choose` is what the proof gives before the book rounds the number of
pairs of forms, `(3T + 2).choose 2`, up to `(3T + 2)² / 2`.

## Main definitions

* `Cslib.Crypto.GenericGroup.dlogGame`: the discrete-logarithm game in the generic group model.

## Main results

* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le`: Theorem 16.3, the bound
  `((3T + 2)² / 2 + 1) / q`.
* `Cslib.Crypto.GenericGroup.succProbability_dlogGame_le_choose`: the sharp form
  `((3T + 2).choose 2 + 1) / q`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 16.3, Theorem 16.3 and its proof, pp. 693–695.
-/

public section

namespace Cslib.Crypto.GenericGroup

open Probability OracleComp
open scoped NNReal ENNReal

variable {q : ℕ} {S : Type}

/-- The discrete-logarithm game in the generic group model ([BonehShoup2023], Theorem 16.3): a
uniform injective labeling `L` and a uniform `α`; the adversary gets `L 1` and `L α`, runs against
the group oracle of `L`, and wins when it outputs `α`. -/
noncomputable def dlogGame [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)) : Game := do
  let L ← PMF.uniformOfFintype (ZMod q ↪ S)
  let α ← PMF.uniformOfFintype (ZMod q)
  let guess ← runLabeled L (A (L 1) (L α))
  return decide (guess = α)

/-! ### Reduction to a uniform permutation as labeling -/

/-- The game with labels in `ZMod q` and a uniform permutation as labeling. -/
private noncomputable def permDlogGame [NeZero q]
    (A : ZMod q → ZMod q → ProbOracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) : Game := do
  let σ ← PMF.uniformOfFintype (Equiv.Perm (ZMod q))
  let α ← PMF.uniformOfFintype (ZMod q)
  let guess ← runLabeled (σ : ZMod q → ZMod q) (A (σ 1) (σ α))
  return decide (guess = α)

private theorem dlogGame_eq_bind_permDlogGame [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)) :
    dlogGame A = (PMF.uniformOfFintype (ZMod q ↪ S)).bind fun j =>
      permDlogGame fun g u => relabel j (A (j g) (j u)) := by
  unfold dlogGame permDlogGame
  simp only [PMF.monad_bind_eq_bind]
  rw [PMF.uniformOfFintype_embedding_bind_perm_trans]
  refine congrArg _ (funext fun j => congrArg _ (funext fun σ => congrArg _ (funext fun α => ?_)))
  rw [runLabeled_relabel]
  rfl

/-! ### Where primality is used -/

/-- Two distinct linear forms over `ZMod q`, `q` prime, agree at no more than one point. -/
private theorem card_filter_affine_eq_le_one [NeZero q] (hq : q.Prime) {c d c' d' : ZMod q}
    (h : (c, d) ≠ (c', d')) :
    (Finset.univ.filter fun α : ZMod q => c * α + d = c' * α + d').card ≤ 1 := by
  have : Fact q.Prime := ⟨hq⟩
  rw [Finset.card_le_one]
  intro a ha b hb
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  by_cases hc : c = c'
  · subst hc
    exact absurd (by simpa using ha : d = d') fun hd => h (by rw [hd])
  · have hne : c - c' ≠ 0 := sub_ne_zero.mpr hc
    exact mul_left_cancel₀ hne (by linear_combination ha - hb)

/-! ### Keyed tables

The core bound follows the book's Games 1 and 2. A *key* `(c, d) : ZMod q × ZMod q` stands for the
linear form `c X + d`, and a table records (key, label) pairs. Two primitive queries act on a
table: `fwd K` asks for the label of the key `K`, and `inv ℓ` for the key of the label `ℓ`; a
group query is at most three of them (`toPrim`). The *real* handler (`realStep`) answers as a
lazily sampled permutation of values at `α`. The *symbolic* handler (`symStep`) gives fresh labels
to fresh keys and new constants to unknown labels; it looks at `α` only to raise a flag when two
distinct keys agree at `α`. The two handlers agree until the flag is raised. -/

/-- The value of the linear form `K = (c, d)`, that is `c X + d`, at `α`. -/
private def ev (α : ZMod q) (K : ZMod q × ZMod q) : ZMod q := K.1 * α + K.2

/-- A table of (key, label) pairs. -/
private abbrev Tab (q : ℕ) := List ((ZMod q × ZMod q) × ZMod q)

/-- The primitive queries on a table: the label of a key, and the key of a label. -/
private inductive Prim (q : ℕ) where
  | fwd (K : ZMod q × ZMod q)
  | inv (ℓ : ZMod q)

/-- The reply types of the primitive queries. -/
private abbrev PrimSpec (q : ℕ) : OracleSpec (Prim q)
  | .fwd _ => ZMod q
  | .inv _ => ZMod q × ZMod q

/-- The cache of a lazily sampled permutation that the table stands for at `α`. -/
private def rep (α : ZMod q) (tab : Tab q) : RandomPermutation.Cache (ZMod q) :=
  tab.map fun e => (ev α e.1, e.2)

private theorem rep_cons (α : ZMod q) (e : (ZMod q × ZMod q) × ZMod q) (tab : Tab q) :
    rep α (e :: tab) = (ev α e.1, e.2) :: rep α tab :=
  rfl

/-- The key of the label `ℓ` in the table. -/
private def keyOf (tab : Tab q) (ℓ : ZMod q) : Option (ZMod q × ZMod q) :=
  (tab.map Prod.swap).lookup ℓ

/-- Some key of the table other than `K` agrees with `K` at `α`. -/
private def Clash (α : ZMod q) (tab : Tab q) (K : ZMod q × ZMod q) : Prop :=
  ∃ e ∈ tab, e.1 ≠ K ∧ ev α e.1 = ev α K

private instance (α : ZMod q) (tab : Tab q) (K : ZMod q × ZMod q) :
    Decidable (Clash α tab K) := by
  unfold Clash; infer_instance

/-- Two distinct keys of the table agree at `α`. -/
private def Collides (α : ZMod q) (tab : Tab q) : Prop :=
  ∃ e ∈ tab, ∃ e' ∈ tab, e.1 ≠ e'.1 ∧ ev α e.1 = ev α e'.1

private instance (α : ZMod q) (tab : Tab q) : Decidable (Collides α tab) := by
  unfold Collides; infer_instance

/-- A table whose values at `α` are distinct and whose labels are distinct: a partial bijection
between values and labels. -/
private def Consistent (α : ZMod q) (tab : Tab q) : Prop :=
  (tab.map fun e => ev α e.1).Nodup ∧ (tab.map Prod.snd).Nodup

private theorem ev_zero_left (α b : ZMod q) : ev α (0, b) = b := by
  simp [ev]

private theorem lookup_eq_none_iff' {β γ : Type} [BEq β] [LawfulBEq β] {l : List (β × γ)}
    {k : β} : l.lookup k = none ↔ ∀ e ∈ l, e.1 ≠ k := by
  simp only [List.lookup_eq_none_iff, bne_iff_ne, ne_comm]

private theorem keyOf_eq_none_iff {tab : Tab q} {ℓ : ZMod q} :
    keyOf tab ℓ = none ↔ ℓ ∉ tab.map Prod.snd := by
  simp only [keyOf, lookup_eq_none_iff', List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, Prod.fst_swap, not_exists, not_and]

private theorem invLookup_rep (α : ZMod q) (tab : Tab q) (ℓ : ZMod q) :
    RandomPermutation.invLookup (rep α tab) ℓ = (keyOf tab ℓ).map (ev α) := by
  unfold RandomPermutation.invLookup rep keyOf
  induction tab with
  | nil => rfl
  | cons e tab ih =>
    obtain ⟨K, m⟩ := e
    simp only [List.map_cons, Prod.swap_prod_mk, List.lookup_cons]
    cases h : (ℓ == m) with
    | true => rfl
    | false => exact ih

/-- In a table with distinct values at `α`, the value of a key finds the key's own label. -/
private theorem lookup_rep_of_lookup {α : ZMod q} {tab : Tab q}
    (hval : (tab.map fun e => ev α e.1).Nodup) {K : ZMod q × ZMod q} {ℓ : ZMod q}
    (h : tab.lookup K = some ℓ) : (rep α tab).lookup (ev α K) = some ℓ := by
  induction tab with
  | nil => simp at h
  | cons e tab ih =>
    obtain ⟨K', m⟩ := e
    rw [List.map_cons, List.nodup_cons] at hval
    simp only [rep, List.map_cons, List.lookup_cons] at h ⊢
    by_cases hK : K = K'
    · subst hK
      simp only [beq_self_eq_true, Option.some.injEq] at h
      simp [h]
    · rw [beq_false_of_ne hK] at h
      have hmem : ev α K ∈ tab.map fun e => ev α e.1 :=
        List.mem_map.mpr ⟨(K, ℓ), List.mem_of_lookup_eq_some h, rfl⟩
      have hne : ev α K ≠ ev α K' := fun heq => hval.1 (heq ▸ hmem)
      rw [beq_false_of_ne hne]
      exact ih hval.2 h

section Tables

variable [NeZero q]

/-- The labels not in the table. -/
private def freshLabels (tab : Tab q) : Finset (ZMod q) :=
  Finset.univ.filter fun ℓ => ℓ ∉ tab.map Prod.snd

/-- The constants `b` such that the constant form `(0, b)` is not a key of the table. -/
private def freshConsts (tab : Tab q) : Finset (ZMod q) :=
  Finset.univ.filter fun b => ((0 : ZMod q), b) ∉ tab.map Prod.fst

/-- The values that no key of the table takes at `α`. -/
private def freshValues (α : ZMod q) (tab : Tab q) : Finset (ZMod q) :=
  Finset.univ.filter fun x => x ∉ tab.map fun e => ev α e.1

/-- A uniform element of `s`, or of `ZMod q` when `s` is empty. -/
private noncomputable def draw (s : Finset (ZMod q)) : PMF (ZMod q) :=
  if h : s.Nonempty then PMF.uniformOfFinset s h else PMF.uniformOfFintype (ZMod q)

private theorem draw_of_nonempty {s : Finset (ZMod q)} (h : s.Nonempty) :
    draw s = PMF.uniformOfFinset s h := by
  simp only [draw, h, ↓reduceDIte]

private theorem mem_of_mem_support_draw {s : Finset (ZMod q)} (h : s.Nonempty) {x : ZMod q}
    (hx : x ∈ (draw s).support) : x ∈ s := by
  rwa [draw_of_nonempty h, PMF.mem_support_uniformOfFinset_iff] at hx

/-- A list shorter than `q` misses some element of `ZMod q`. -/
private theorem exists_notMem_of_length_lt {l : List (ZMod q)} (h : l.length < q) :
    ∃ x, x ∉ l :=
  let ⟨x, _, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card (s := l.toFinset)
    (t := Finset.univ) ((List.toFinset_card_le l).trans_lt (by rwa [Finset.card_univ, ZMod.card]))
  ⟨x, fun hmem => hx (List.mem_toFinset.mpr hmem)⟩

private theorem length_lt_of_notMem {l : List (ZMod q)} (hl : l.Nodup) {x : ZMod q}
    (hx : x ∉ l) : l.length < q := by
  have := (List.nodup_cons.mpr ⟨hx, hl⟩).length_le_card
  rw [ZMod.card, List.length_cons] at this
  omega

private theorem freshLabels_nonempty {tab : Tab q} (h : tab.length < q) :
    (freshLabels tab).Nonempty := by
  obtain ⟨x, hx⟩ := exists_notMem_of_length_lt (l := tab.map Prod.snd) (by simpa using h)
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

private theorem freshValues_nonempty (α : ZMod q) {tab : Tab q} (h : tab.length < q) :
    (freshValues α tab).Nonempty := by
  obtain ⟨x, hx⟩ :=
    exists_notMem_of_length_lt (l := tab.map fun e => ev α e.1) (by simpa using h)
  exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩

private theorem freshConsts_nonempty {tab : Tab q} (h : tab.length < q) :
    (freshConsts tab).Nonempty := by
  obtain ⟨b, hb⟩ := exists_notMem_of_length_lt (l := tab.map fun e => e.1.2) (by simpa using h)
  refine ⟨b, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun hmem => hb ?_⟩⟩
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  exact List.mem_map.mpr ⟨e, he, by rw [heq]⟩

/-- An unused value is an unused constant: the constant form `(0, x)` takes the value `x`. -/
private theorem freshValues_subset_freshConsts (α : ZMod q) (tab : Tab q) :
    freshValues α tab ⊆ freshConsts tab := by
  intro x hx
  simp only [freshValues, freshConsts, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  intro hmem
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
  exact hx (List.mem_map.mpr ⟨e, he, by rw [heq, ev_zero_left]⟩)

/-- For an unused constant `b`, the constant form `(0, b)` clashes exactly when `b` is a used
value. -/
private theorem clash_iff_notMem_freshValues {α : ZMod q} {tab : Tab q} {b : ZMod q}
    (hb : b ∈ freshConsts tab) : Clash α tab (0, b) ↔ b ∉ freshValues α tab := by
  simp only [freshConsts, freshValues, Finset.mem_filter, Finset.mem_univ, true_and,
    not_not] at hb ⊢
  constructor
  · rintro ⟨e, he, -, heq⟩
    exact List.mem_map.mpr ⟨e, he, by rw [heq, ev_zero_left]⟩
  · intro hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    refine ⟨e, he, fun hK => hb (List.mem_map.mpr ⟨e, he, hK⟩), by rw [heq, ev_zero_left]⟩

private theorem unusedRange_rep (α : ZMod q) (tab : Tab q) :
    RandomPermutation.unusedRange (rep α tab) = freshLabels tab := by
  ext y
  simp only [RandomPermutation.unusedRange, freshLabels, Finset.mem_filter, Finset.mem_univ,
    true_and, RandomPermutation.invLookup_eq_none_iff, rep, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, not_exists, not_and]

private theorem unusedDomain_rep (α : ZMod q) (tab : Tab q) :
    RandomPermutation.unusedDomain (rep α tab) = freshValues α tab := by
  ext x
  simp only [RandomPermutation.unusedDomain, freshValues, Finset.mem_filter, Finset.mem_univ,
    true_and, RandomPermutation.lookup_eq_none_iff, rep, List.mem_map, forall_exists_index,
    and_imp, forall_apply_eq_imp_iff₂, not_exists, not_and]

private theorem answer_forward_of_some {c : RandomPermutation.Cache (ZMod q)} {x y : ZMod q}
    (h : c.lookup x = some y) :
    RandomPermutation.answer (.forward x) c = PMF.pure (y, c) := by
  simp only [RandomPermutation.answer, h]

private theorem answer_forward_of_none {c : RandomPermutation.Cache (ZMod q)} {x : ZMod q}
    (h : c.lookup x = none) :
    RandomPermutation.answer (.forward x) c =
      (draw (RandomPermutation.unusedRange c)).map fun y => (y, (x, y) :: c) := by
  simp only [RandomPermutation.answer, h, draw]
  split_ifs <;> rfl

private theorem answer_inverse_of_some {c : RandomPermutation.Cache (ZMod q)} {x y : ZMod q}
    (h : RandomPermutation.invLookup c y = some x) :
    RandomPermutation.answer (.inverse y) c = PMF.pure (x, c) := by
  simp only [RandomPermutation.answer, h]

private theorem answer_inverse_of_none {c : RandomPermutation.Cache (ZMod q)} {y : ZMod q}
    (h : RandomPermutation.invLookup c y = none) :
    RandomPermutation.answer (.inverse y) c =
      (draw (RandomPermutation.unusedDomain c)).map fun x => (x, (x, y) :: c) := by
  simp only [RandomPermutation.answer, h, draw]
  split_ifs <;> rfl

/-! #### The two handlers -/

/-- One step of the symbolic handler, with its flag. A known key or label gets its entry. A new
key gets a uniform unused label; a new label gets a uniform new constant form. The flag records
that the new key agrees at `α` with a key already in the table. -/
private noncomputable def symStep (α : ZMod q) :
    (p : Prim q) → Tab q → PMF (PrimSpec q p × (Tab q × Bool))
  | .fwd K, tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab, false)
    | none => (draw (freshLabels tab)).map fun ℓ =>
        (ℓ, (K, ℓ) :: tab, ((rep α tab).lookup (ev α K)).isSome)
  | .inv ℓ, tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab, false)
    | none => (draw (freshConsts tab)).map fun b =>
        (((0 : ZMod q), b), ((0, b), ℓ) :: tab, decide (Clash α tab (0, b)))

/-- One step of the real handler, with its flag. It differs from `symStep` only where the flag is
raised: a new key whose value at `α` is already taken gets that value's label, and a new constant
whose value is already taken is redrawn among the unused values. -/
private noncomputable def realStep (α : ZMod q) :
    (p : Prim q) → Tab q → PMF (PrimSpec q p × (Tab q × Bool))
  | .fwd K, tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab, false)
    | none =>
      match (rep α tab).lookup (ev α K) with
      | some ℓ => PMF.pure (ℓ, tab, true)
      | none => (draw (freshLabels tab)).map fun ℓ => (ℓ, (K, ℓ) :: tab, false)
  | .inv ℓ, tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab, false)
    | none => (draw (freshConsts tab)).bind fun b =>
        if Clash α tab (0, b) then
          (draw (freshValues α tab)).map fun b' => (((0 : ZMod q), b'), ((0, b'), ℓ) :: tab, true)
        else PMF.pure (((0 : ZMod q), b), ((0, b), ℓ) :: tab, false)

/-- The symbolic handler without its flag. It does not depend on `α`. -/
private noncomputable def symOracle : (p : Prim q) → StateT (Tab q) PMF (PrimSpec q p)
  | .fwd K => fun tab =>
    match tab.lookup K with
    | some ℓ => PMF.pure (ℓ, tab)
    | none => (draw (freshLabels tab)).map fun ℓ => (ℓ, (K, ℓ) :: tab)
  | .inv ℓ => fun tab =>
    match keyOf tab ℓ with
    | some K => PMF.pure (K, tab)
    | none => (draw (freshConsts tab)).map fun b => (((0 : ZMod q), b), ((0, b), ℓ) :: tab)

/-! #### One step of each handler -/

/-- A forward step of the real handler, read at `α`, is a forward query to the lazy permutation. -/
private theorem realStep_fwd_map {α : ZMod q} {tab : Tab q}
    (hval : (tab.map fun e => ev α e.1).Nodup) (K : ZMod q × ZMod q) :
    (realStep α (.fwd K) tab).map (fun x => (x.1, rep α x.2.1)) =
      RandomPermutation.answer (.forward (ev α K)) (rep α tab) := by
  rcases h₁ : tab.lookup K with _ | ℓ
  · rcases h₂ : (rep α tab).lookup (ev α K) with _ | ℓ
    · simp only [realStep, h₁, h₂, PMF.map_comp, answer_forward_of_none h₂, unusedRange_rep]
      rfl
    · simp only [realStep, h₁, h₂, PMF.pure_map, answer_forward_of_some h₂]
  · simp only [realStep, h₁, PMF.pure_map, answer_forward_of_some (lookup_rep_of_lookup hval h₁)]

/-- An inverse step of the real handler, read at `α`, is an inverse query to the lazy
permutation: a redrawn constant is uniform among the unused values (`PMF.unifOn_rehash_eq`). -/
private theorem realStep_inv_map {α : ZMod q} {tab : Tab q} (hcon : Consistent α tab)
    (ℓ : ZMod q) :
    (realStep α (.inv ℓ) tab).map (fun x => (ev α x.1, rep α x.2.1)) =
      RandomPermutation.answer (.inverse ℓ) (rep α tab) := by
  rcases h : keyOf tab ℓ with _ | K
  · have hinv : RandomPermutation.invLookup (rep α tab) ℓ = none := by
      rw [invLookup_rep, h]; rfl
    have hlen : tab.length < q := by
      simpa using length_lt_of_notMem hcon.2 (keyOf_eq_none_iff.mp h)
    have hc := freshConsts_nonempty hlen
    have hv := freshValues_nonempty α hlen
    rw [answer_inverse_of_none hinv, unusedDomain_rep, draw_of_nonempty hv,
      ← PMF.unifOn_rehash_eq (freshValues_subset_freshConsts α tab) hc hv, PMF.map_bind]
    simp only [realStep, h, draw_of_nonempty hc, PMF.map_bind]
    refine PMF.bind_congr_on_support _ _ _ fun b hb => ?_
    rw [PMF.mem_support_uniformOfFinset_iff] at hb
    by_cases hcl : Clash α tab (0, b)
    · have hbv : b ∉ freshValues α tab := (clash_iff_notMem_freshValues hb).mp hcl
      rw [ite_eq_left hcl, ite_eq_right hbv, draw_of_nonempty hv, PMF.map_comp]
      congr 1
      funext b'
      simp [rep_cons, ev_zero_left]
    · have hbv : b ∈ freshValues α tab :=
        not_not.mp (mt (clash_iff_notMem_freshValues hb).mpr hcl)
      rw [ite_eq_right hcl, ite_eq_left hbv, PMF.pure_map, PMF.pure_map]
      simp [rep_cons, ev_zero_left]
  · have hinv : RandomPermutation.invLookup (rep α tab) ℓ = some (ev α K) := by
      rw [invLookup_rep, h]; rfl
    simp only [realStep, h, PMF.pure_map, answer_inverse_of_some hinv]

/-- The real handler keeps tables consistent. -/
private theorem consistent_of_mem_support_realStep {α : ZMod q} {tab : Tab q}
    (hcon : Consistent α tab) (p : Prim q) {x : PrimSpec q p × (Tab q × Bool)}
    (hx : x ∈ (realStep α p tab).support) : Consistent α x.2.1 := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · rcases h₂ : (rep α tab).lookup (ev α K) with _ | ℓ
      · simp only [realStep, h₁, h₂, PMF.mem_support_map_iff] at hx
        obtain ⟨ℓ, hℓ, rfl⟩ := hx
        have hK : ev α K ∉ tab.map fun e => ev α e.1 := by
          intro hmem
          obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
          exact lookup_eq_none_iff'.mp h₂ (ev α e.1, e.2) (List.mem_map.mpr ⟨e, he, rfl⟩) heq
        have hlen : tab.length < q := by simpa using length_lt_of_notMem hcon.1 hK
        have hℓ' := mem_of_mem_support_draw (freshLabels_nonempty hlen) hℓ
        simp only [freshLabels, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ'
        exact ⟨List.nodup_cons.mpr ⟨hK, hcon.1⟩, List.nodup_cons.mpr ⟨hℓ', hcon.2⟩⟩
      · simp only [realStep, h₁, h₂, PMF.mem_support_pure_iff] at hx
        subst hx; exact hcon
    · simp only [realStep, h₁, PMF.mem_support_pure_iff] at hx
      subst hx; exact hcon
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · have hℓ : ℓ ∉ tab.map Prod.snd := keyOf_eq_none_iff.mp h
      have hlen : tab.length < q := by simpa using length_lt_of_notMem hcon.2 hℓ
      simp only [realStep, h, PMF.mem_support_bind_iff] at hx
      obtain ⟨b, hb, hx⟩ := hx
      have hb' := mem_of_mem_support_draw (freshConsts_nonempty hlen) hb
      by_cases hcl : Clash α tab (0, b)
      · rw [ite_eq_left hcl, PMF.mem_support_map_iff] at hx
        obtain ⟨b', hb'', rfl⟩ := hx
        have hv := mem_of_mem_support_draw (freshValues_nonempty α hlen) hb''
        simp only [freshValues, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨List.nodup_cons.mpr ⟨?_, hcon.1⟩, List.nodup_cons.mpr ⟨hℓ, hcon.2⟩⟩
        change ev α (0, b') ∉ _
        rwa [ev_zero_left]
      · rw [ite_eq_right hcl, PMF.mem_support_pure_iff] at hx
        subst hx
        have hv : b ∈ freshValues α tab :=
          not_not.mp (mt (clash_iff_notMem_freshValues hb').mpr hcl)
        simp only [freshValues, Finset.mem_filter, Finset.mem_univ, true_and] at hv
        refine ⟨List.nodup_cons.mpr ⟨?_, hcon.1⟩, List.nodup_cons.mpr ⟨hℓ, hcon.2⟩⟩
        change ev α (0, b) ∉ _
        rwa [ev_zero_left]
    · simp only [realStep, h, PMF.mem_support_pure_iff] at hx
      subst hx; exact hcon

omit [NeZero q] in
/-- An outcome with a lowered flag has probability zero under a distribution that always raises
it. -/
private theorem apply_eq_zero_of_flag {β : Type} {p : PMF (β × (Tab q × Bool))}
    (hp : ∀ y ∈ p.support, y.2.2 = true) (a : β) (tab' : Tab q) : p (a, (tab', false)) = 0 :=
  (PMF.apply_eq_zero_iff _ _).mpr fun hmem => by simpa using hp _ hmem

/-- The real and symbolic steps give every outcome with a lowered flag the same probability. -/
private theorem realStep_agree (α : ZMod q) (p : Prim q) (tab : Tab q) (a : PrimSpec q p)
    (tab' : Tab q) :
    realStep α p tab (a, (tab', false)) = symStep α p tab (a, (tab', false)) := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · rcases h₂ : (rep α tab).lookup (ev α K) with _ | ℓ
      · simp only [realStep, symStep, h₁, h₂, Option.isSome_none]
      · simp only [realStep, symStep, h₁, h₂, Option.isSome_some]
        rw [apply_eq_zero_of_flag (by simp) a tab', apply_eq_zero_of_flag (by simp) a tab']
    · simp only [realStep, symStep, h₁]
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · simp only [realStep, symStep, h]
      rw [PMF.bind_apply, ← PMF.bind_pure_comp _ (draw (freshConsts tab)), PMF.bind_apply]
      refine tsum_congr fun b => congrArg _ ?_
      by_cases hcl : Clash α tab (0, b)
      · simp only [hcl, ↓reduceIte, Function.comp_apply, decide_true]
        rw [apply_eq_zero_of_flag (by simp) a tab', apply_eq_zero_of_flag (by simp) a tab']
      · simp only [hcl, ↓reduceIte, Function.comp_apply, decide_false]
    · simp only [realStep, symStep, h]

/-- Dropping the flag of the symbolic step leaves `symOracle`. -/
private theorem symStep_map_fst (α : ZMod q) (p : Prim q) (tab : Tab q) :
    (symStep α p tab).map (Prod.map id Prod.fst) = symOracle p tab := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · simp only [symStep, symOracle, h₁, PMF.map_comp]; rfl
    · simp only [symStep, symOracle, h₁, PMF.pure_map]; rfl
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · simp only [symStep, symOracle, h, PMF.map_comp]; rfl
    · simp only [symStep, symOracle, h, PMF.pure_map]; rfl

omit [NeZero q] in
private theorem Collides.mono {α : ZMod q} {tab tab' : Tab q} (h : ∀ e ∈ tab, e ∈ tab')
    (hc : Collides α tab) : Collides α tab' := by
  obtain ⟨e, he, e', he', hne, heq⟩ := hc
  exact ⟨e, h e he, e', h e' he', hne, heq⟩

/-- The symbolic step only adds to the table, and raises its flag only when the new table has two
distinct keys that agree at `α`. -/
private theorem symStep_support {α : ZMod q} {tab : Tab q} (p : Prim q)
    {x : PrimSpec q p × (Tab q × Bool)} (hx : x ∈ (symStep α p tab).support) :
    (∀ e ∈ tab, e ∈ x.2.1) ∧ (x.2.2 = true → Collides α x.2.1) := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · simp only [symStep, h₁, PMF.mem_support_map_iff] at hx
      obtain ⟨ℓ, -, rfl⟩ := hx
      refine ⟨fun e he => List.mem_cons_of_mem _ he, fun hflag => ?_⟩
      obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp hflag
      obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_of_lookup_eq_some hm)
      simp only [Prod.mk.injEq] at heq
      exact ⟨e, List.mem_cons_of_mem _ he, (K, ℓ), List.mem_cons_self,
        lookup_eq_none_iff'.mp h₁ e he, heq.1⟩
    · simp only [symStep, h₁, PMF.mem_support_pure_iff] at hx
      subst hx
      exact ⟨fun e he => he, fun h => absurd h (by simp)⟩
  | inv ℓ =>
    rcases h : keyOf tab ℓ with _ | K
    · simp only [symStep, h, PMF.mem_support_map_iff] at hx
      obtain ⟨b, -, rfl⟩ := hx
      refine ⟨fun e he => List.mem_cons_of_mem _ he, fun hflag => ?_⟩
      obtain ⟨e, he, hne, heq⟩ := of_decide_eq_true hflag
      exact ⟨e, List.mem_cons_of_mem _ he, ((0, b), ℓ), List.mem_cons_self, hne, heq⟩
    · simp only [symStep, h, PMF.mem_support_pure_iff] at hx
      subst hx
      exact ⟨fun e he => he, fun h => absurd h (by simp)⟩

/-- A raised flag of the symbolic handler means that two distinct keys agree at `α`. -/
private theorem symFlag_preserve (α : ZMod q) (p : Prim q) (s : Tab q × Bool)
    (hs : s.2 = true → Collides α s.1) (a : PrimSpec q p) (s' : Tab q × Bool)
    (h : (a, s') ∈ (withBadFlag (symStep α) p s).support) : s'.2 = true → Collides α s'.1 := by
  obtain ⟨tab, b⟩ := s
  simp only [withBadFlag, PMF.mem_support_map_iff] at h
  obtain ⟨x, hx, heq⟩ := h
  obtain ⟨hsub, hflag⟩ := symStep_support p hx
  simp only [Prod.map, id, Prod.mk.injEq] at heq
  obtain ⟨-, rfl⟩ := heq
  intro hb
  rcases Bool.or_eq_true_iff.mp hb with hb | hb
  · exact (hs hb).mono hsub
  · exact hflag hb

/-- The symbolic step adds at most one entry. -/
private theorem length_le_of_mem_support_symOracle (p : Prim q) (tab : Tab q)
    (a : PrimSpec q p) (tab' : Tab q) (h : (a, tab') ∈ (symOracle p tab).support) :
    tab'.length ≤ tab.length + 1 := by
  cases p with
  | fwd K =>
    rcases h₁ : tab.lookup K with _ | ℓ
    · simp only [symOracle, h₁, PMF.mem_support_map_iff] at h
      obtain ⟨ℓ, -, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      rw [← heq.2, List.length_cons]
    · simp only [symOracle, h₁, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      rw [h.2]; omega
  | inv ℓ =>
    rcases h₂ : keyOf tab ℓ with _ | K
    · simp only [symOracle, h₂, PMF.mem_support_map_iff] at h
      obtain ⟨b, -, heq⟩ := h
      simp only [Prod.mk.injEq] at heq
      rw [← heq.2, List.length_cons]
    · simp only [symOracle, h₂, PMF.mem_support_pure_iff, Prod.mk.injEq] at h
      rw [h.2]; omega

end Tables

/-! #### Group queries as primitive queries -/

/-- The key of the form `κ₁ K₁ + κ₂ K₂`. -/
private def comb (κ₁ : ZMod q) (K₁ : ZMod q × ZMod q) (κ₂ : ZMod q) (K₂ : ZMod q × ZMod q) :
    ZMod q × ZMod q :=
  (κ₁ * K₁.1 + κ₂ * K₂.1, κ₁ * K₁.2 + κ₂ * K₂.2)

private theorem ev_comb (α κ₁ κ₂ : ZMod q) (K₁ K₂ : ZMod q × ZMod q) :
    ev α (comb κ₁ K₁ κ₂ K₂) = κ₁ * ev α K₁ + κ₂ * ev α K₂ := by
  simp only [ev, comb]
  ring

private theorem ev_one_zero (α : ZMod q) : ev α (1, 0) = α := by
  simp [ev]

/-- A group query as primitive queries: a labeling query asks for the label of a constant form; a
group operation asks for the keys of its two labels, then for the label of the combined key. -/
private def toPrim : (query : GroupQuery q (ZMod q)) →
    OracleComp (PrimSpec q) (GroupOracleSpec q (ZMod q) query)
  | .label β => OracleComp.query (spec := PrimSpec q) (.fwd (0, β))
  | .op ℓ₁ ℓ₂ κ₁ κ₂ => do
    let K₁ ← OracleComp.query (spec := PrimSpec q) (.inv ℓ₁)
    let K₂ ← OracleComp.query (spec := PrimSpec q) (.inv ℓ₂)
    let ℓ ← OracleComp.query (spec := PrimSpec q) (.fwd (comb κ₁ K₁ κ₂ K₂))
    return some ℓ

/-- A group query as queries to a permutation used as labeling: a labeling query evaluates it; a
group operation inverts it on the two labels and evaluates it on the combination. -/
private def toPerm : (query : GroupQuery q (ZMod q)) →
    OracleComp (RandomPermutation.PermOracleSpec (ZMod q)) (GroupOracleSpec q (ZMod q) query)
  | .label β => OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.forward β)
  | .op ℓ₁ ℓ₂ κ₁ κ₂ => do
    let x₁ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.inverse ℓ₁)
    let x₂ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.inverse ℓ₂)
    let ℓ ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q))
      (.forward (κ₁ * x₁ + κ₂ * x₂))
    return some ℓ

/-- The adversary `D` on primitive queries: its generator and challenge are the labels of the forms
`1` and `X`. -/
private def primGame (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    OracleComp (PrimSpec q) (ZMod q) := do
  let g ← OracleComp.query (spec := PrimSpec q) (.fwd (0, 1))
  let u ← OracleComp.query (spec := PrimSpec q) (.fwd (1, 0))
  OracleComp.interpret toPrim (D g u)

/-- The adversary `D` on permutation queries: its generator and challenge are the labels of `1` and
`α`. -/
private def permGame (α : ZMod q)
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    OracleComp (RandomPermutation.PermOracleSpec (ZMod q)) (ZMod q) := do
  let g ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.forward 1)
  let u ← OracleComp.query (spec := RandomPermutation.PermOracleSpec (ZMod q)) (.forward α)
  OracleComp.interpret toPerm (D g u)

/-- `primGame D` makes at most `3T + 2` primitive queries: two for the inputs and at most three
for each group query. -/
private theorem isQueryBounded_primGame {T : ℕ}
    {D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)}
    (hD : ∀ g u, (D g u).IsQueryBounded T) : (primGame D).IsQueryBounded (3 * T + 2) := by
  have hquery (p : Prim q) : (OracleComp.query (spec := PrimSpec q) p).IsQueryBounded 1 :=
    IsCostBounded.query p
  have htoPrim : ∀ query : GroupQuery q (ZMod q),
      (toPrim query).IsQueryBounded ((fun _ : GroupQuery q (ZMod q) => 3) query) := by
    intro query
    cases query with
    | label β => exact (hquery _).mono (by norm_num)
    | op ℓ₁ ℓ₂ κ₁ κ₂ =>
      exact ((hquery _).bind fun _ => (hquery _).bind fun _ =>
        (hquery _).bind fun _ => IsCostBounded.pure _ 0).mono (by norm_num)
  have hD' (g u : ZMod q) :
      IsCostBounded (fun _ : GroupQuery q (ZMod q) => 3) (D g u) (T * 3) :=
    (hD g u).isCostBounded_mul_of_forall_le fun _ => le_rfl
  have h := (hquery (.fwd (0, 1))).bind fun g => (hquery (.fwd (1, 0))).bind fun u =>
    IsCostBounded.interpret htoPrim (hD' g u)
  exact h.mono (by omega)

/-- Against a permutation `σ`, the permutation queries of `toPerm` answer as the group oracle of
`σ`. -/
private theorem interpret_evalPerm_toPerm (σ : Equiv.Perm (ZMod q))
    (query : GroupQuery q (ZMod q)) :
    OracleComp.interpret (fun p => PMF.pure (RandomPermutation.evalPerm σ p)) (toPerm query) =
      PMF.pure (answer σ query) := by
  cases query with
  | label β =>
    simp [toPerm]
  | op ℓ₁ ℓ₂ κ₁ κ₂ =>
    obtain ⟨β₁, rfl⟩ := σ.surjective ℓ₁
    obtain ⟨β₂, rfl⟩ := σ.surjective ℓ₂
    simp [toPerm, answer_op_label σ.injective, Probability.PMF.monad_bind_eq_bind]

private theorem interpret_evalPerm_permGame (σ : Equiv.Perm (ZMod q)) (α : ZMod q)
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    OracleComp.interpret (fun p => PMF.pure (RandomPermutation.evalPerm σ p)) (permGame α D) =
      OracleComp.interpret (fun query => PMF.pure (answer σ query)) (D (σ 1) (σ α)) := by
  simp only [permGame, OracleComp.interpret_bind, OracleComp.interpret_query,
    OracleComp.interpret_interpret, interpret_evalPerm_toPerm, RandomPermutation.evalPerm_forward,
    Probability.PMF.monad_bind_eq_bind, PMF.pure_bind]

/-- One step of a sequential composition, read through `r`, is a step of another, when the first
stages correspond through `φ` and `r` and every continuation from a state satisfying `I` does. -/
private theorem map_bind_eq_of_step {A A' B σ σ' : Type} (φ : A → A') (r : σ → σ') (I : σ → Prop)
    {m : PMF (A × σ)} {m' : PMF (A' × σ')} (hm : m.map (fun x => (φ x.1, r x.2)) = m')
    (hI : ∀ x ∈ m.support, I x.2) (f : A × σ → PMF (B × σ)) (f' : A' × σ' → PMF (B × σ'))
    (hf : ∀ a s, I s → (f (a, s)).map (fun x => (x.1, r x.2)) = f' (φ a, r s)) :
    (m.bind f).map (fun x => (x.1, r x.2)) = m'.bind f' := by
  rw [PMF.map_bind, ← hm, PMF.bind_map]
  exact PMF.bind_congr_on_support _ _ _ fun x hx => hf x.1 x.2 (hI x hx)

/-- The probability that a Boolean test accepts is the probability of the event it tests. -/
private theorem bind_pure_decide_apply_true {β : Type} (p : PMF β) (P : β → Prop)
    [DecidablePred P] :
    (p.bind fun x => PMF.pure (decide (P x))) true = p.toOuterMeasure {x | P x} := by
  rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases hx : P x <;> simp [hx]

section Games

variable [NeZero q]

private theorem consistent_of_mem_support_withBadFlag {α : ZMod q} {s : Tab q × Bool}
    (hs : Consistent α s.1) (p : Prim q) {x : PrimSpec q p × (Tab q × Bool)}
    (h : x ∈ (withBadFlag (realStep α) p s).support) : Consistent α x.2.1 := by
  obtain ⟨tab, b⟩ := s
  simp only [withBadFlag, PMF.mem_support_map_iff] at h
  obtain ⟨y, hy, rfl⟩ := h
  exact (consistent_of_mem_support_realStep hs p hy :)

private theorem realFl_fwd_map {α : ZMod q} {s : Tab q × Bool} (hs : Consistent α s.1)
    (K : ZMod q × ZMod q) :
    ((withBadFlag (realStep α) (.fwd K)).run s).map (fun x => (x.1, rep α x.2.1)) =
      (RandomPermutation.answer (.forward (ev α K))).run (rep α s.1) := by
  obtain ⟨tab, b⟩ := s
  simp only [StateT.run, withBadFlag, PMF.map_comp]
  exact realStep_fwd_map hs.1 K

private theorem realFl_inv_map {α : ZMod q} {s : Tab q × Bool} (hs : Consistent α s.1)
    (ℓ : ZMod q) :
    ((withBadFlag (realStep α) (.inv ℓ)).run s).map (fun x => (ev α x.1, rep α x.2.1)) =
      (RandomPermutation.answer (.inverse ℓ)).run (rep α s.1) := by
  obtain ⟨tab, b⟩ := s
  simp only [StateT.run, withBadFlag, PMF.map_comp]
  exact realStep_inv_map hs ℓ

/-- The real handler on one group query, read at `α`, is the lazy permutation on that query. -/
private theorem realGroup_step (α : ZMod q) (query : GroupQuery q (ZMod q)) (s : Tab q × Bool)
    (hs : Consistent α s.1) :
    ((OracleComp.interpret (withBadFlag (realStep α)) (toPrim query)).run s).map
        (fun x => (x.1, rep α x.2.1)) =
      (OracleComp.interpret RandomPermutation.answer (toPerm query)).run (rep α s.1) := by
  cases query with
  | label β =>
    have h := realFl_fwd_map hs (0, β)
    rw [ev_zero_left] at h
    simpa only [toPrim, toPerm, OracleComp.interpret_query] using h
  | op ℓ₁ ℓ₂ κ₁ κ₂ =>
    simp only [toPrim, toPerm, OracleComp.interpret_bind, OracleComp.interpret_query,
      OracleComp.interpret_pure, StateT.run_bind, StateT.run_pure,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure]
    refine map_bind_eq_of_step (ev α) (fun s : Tab q × Bool => rep α s.1)
      (fun s : Tab q × Bool => Consistent α s.1) (realFl_inv_map hs ℓ₁)
      (fun x hx => consistent_of_mem_support_withBadFlag hs _ hx) _ _ ?_
    intro K₁ s₁ hs₁
    dsimp only
    refine map_bind_eq_of_step (ev α) (fun s : Tab q × Bool => rep α s.1)
      (fun s : Tab q × Bool => Consistent α s.1) (realFl_inv_map hs₁ ℓ₂)
      (fun x hx => consistent_of_mem_support_withBadFlag hs₁ _ hx) _ _ ?_
    intro K₂ s₂ hs₂
    dsimp only
    have h := realFl_fwd_map hs₂ (comb κ₁ K₁ κ₂ K₂)
    rw [ev_comb] at h
    refine map_bind_eq_of_step id (fun s : Tab q × Bool => rep α s.1) (fun _ => True) h
      (fun _ _ => trivial) _ _ ?_
    intro ℓ s₃ _
    simp only [PMF.pure_map, id]

/-- The real handler on `primGame D`, read at `α`, is the lazy permutation on `permGame α D`. -/
private theorem real_eq_lazy (α : ZMod q)
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    ((OracleComp.interpret (withBadFlag (realStep α)) (primGame D)).run ([], false)).map
        (fun x => (x.1, rep α x.2.1)) =
      (OracleComp.interpret RandomPermutation.answer (permGame α D)).run [] := by
  have hgroup (g u : ZMod q) (s : Tab q × Bool) (hs : Consistent α s.1) :
      ((OracleComp.interpret (withBadFlag (realStep α))
          (OracleComp.interpret toPrim (D g u))).run s).map (fun x => (x.1, rep α x.2.1)) =
        (OracleComp.interpret RandomPermutation.answer
          (OracleComp.interpret toPerm (D g u))).run (rep α s.1) := by
    rw [OracleComp.interpret_interpret, OracleComp.interpret_interpret]
    exact OracleComp.run_interpret_map_state_of_invariant _ _
      (fun s : Tab q × Bool => rep α s.1) (fun s : Tab q × Bool => Consistent α s.1)
      (fun query s hs a s' h => OracleComp.run_interpret_invariant _ _
        (fun p s hs a s' h => consistent_of_mem_support_withBadFlag hs p h) (toPrim query) s hs
        a s' h)
      (fun query s hs => realGroup_step α query s hs) (D g u) s hs
  have h0 : Consistent α ([] : Tab q) := ⟨List.nodup_nil, List.nodup_nil⟩
  have h₁ := realFl_fwd_map (s := ([], false)) h0 (0, 1)
  rw [ev_zero_left] at h₁
  simp only [primGame, permGame, OracleComp.interpret_bind, OracleComp.interpret_query,
    StateT.run_bind, Probability.PMF.monad_bind_eq_bind]
  refine map_bind_eq_of_step id (fun s : Tab q × Bool => rep α s.1)
    (fun s : Tab q × Bool => Consistent α s.1) h₁
    (fun x hx => consistent_of_mem_support_withBadFlag (s := ([], false)) h0 _ hx) _ _ ?_
  intro g s₁ hs₁
  dsimp only
  have h₂ := realFl_fwd_map hs₁ (1, 0)
  rw [ev_one_zero] at h₂
  refine map_bind_eq_of_step id (fun s : Tab q × Bool => rep α s.1)
    (fun s : Tab q × Bool => Consistent α s.1) h₂
    (fun x hx => consistent_of_mem_support_withBadFlag hs₁ _ hx) _ _ ?_
  intro u s₂ hs₂
  exact hgroup g u s₂ hs₂

/-- With a uniform permutation as labeling, the group oracle is the real handler on primitive
queries. -/
private theorem uniform_interpret_eq_real (α : ZMod q)
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    (PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind (fun σ =>
        OracleComp.interpret (fun query => PMF.pure (answer σ query)) (D (σ 1) (σ α))) =
      ((OracleComp.interpret (withBadFlag (realStep α)) (primGame D)).run ([], false)).map
        Prod.fst := by
  have h := RandomPermutation.uniform_interpret_eq_lazy (permGame α D)
  simp only [Probability.PMF.monad_bind_eq_bind, interpret_evalPerm_permGame] at h
  rw [h, ← real_eq_lazy α D, PMF.map_comp]
  rfl

/-- The game against a deterministic adversary with a uniform permutation as labeling. -/
private noncomputable def detGame
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) : Game :=
  (PMF.uniformOfFintype (Equiv.Perm (ZMod q))).bind fun σ =>
    (PMF.uniformOfFintype (ZMod q)).bind fun α =>
      (OracleComp.interpret (fun query => PMF.pure (answer σ query)) (D (σ 1) (σ α))).bind
        fun guess => PMF.pure (decide (guess = α))

private theorem detGame_eq
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    detGame D = (PMF.uniformOfFintype (ZMod q)).bind fun α =>
      ((OracleComp.interpret (withBadFlag (realStep α)) (primGame D)).run ([], false)).bind
        fun x => PMF.pure (decide (x.1 = α)) := by
  unfold detGame
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun α => ?_)
  rw [← PMF.bind_bind, uniform_interpret_eq_real, PMF.bind_map]
  rfl

/-- For a fixed `α`, the real game is won at most as often as the symbolic one, plus the
probability that the symbolic table has two distinct keys that agree at `α`. -/
private theorem real_le (α : ZMod q)
    (D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    ((OracleComp.interpret (withBadFlag (realStep α)) (primGame D)).run ([], false)).bind
        (fun x => PMF.pure (decide (x.1 = α))) true ≤
      ((OracleComp.interpret symOracle (primGame D)).run []).bind
          (fun y => PMF.pure (decide (y.1 = α))) true +
        ((OracleComp.interpret symOracle (primGame D)).run []).bind
          (fun y => PMF.pure (decide (Collides α y.2))) true := by
  have hiub := OracleComp.identicalUntilBad_withBadFlag (realStep α) (symStep α) (realStep_agree α)
  have hfst := OracleComp.run_interpret_withBadFlag_map_fst (symStep α) symOracle
    (symStep_map_fst α) (primGame D) [] false
  refine (hiub.bind_apply_le (primGame D) ([], false) _ true).trans ?_
  rw [hiub.bad_eq, ← hfst, PMF.bind_map, PMF.bind_map]
  refine add_le_add le_rfl (le_of_le_of_eq ?_ (bind_pure_decide_apply_true _
    (fun x : ZMod q × (Tab q × Bool) => Collides α x.2.1)).symm)
  refine PMF.toOuterMeasure_mono _ fun x hx => ?_
  exact OracleComp.run_interpret_invariant (withBadFlag (symStep α))
    (fun s => s.2 = true → Collides α s.1) (symFlag_preserve α) (primGame D) ([], false)
    (by simp) x.1 x.2 hx.2 hx.1

end Games

/-- Distinct keys from a set of `n` keys agree at no more than `n.choose 2` points. -/
private theorem card_filter_pairs_le (hq : q.Prime) [NeZero q] (s : Finset (ZMod q × ZMod q)) :
    (Finset.univ.filter fun α : ZMod q =>
      ∃ K ∈ s, ∃ K' ∈ s, K ≠ K' ∧ ev α K = ev α K').card ≤ s.card.choose 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert K s hK ih =>
    rw [Finset.card_insert_of_notMem hK, Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    have hsub : (Finset.univ.filter fun α : ZMod q =>
          ∃ a ∈ insert K s, ∃ b ∈ insert K s, a ≠ b ∧ ev α a = ev α b) ⊆
        (Finset.univ.filter fun α : ZMod q => ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ev α a = ev α b) ∪
          s.biUnion fun K' => Finset.univ.filter fun α : ZMod q => ev α K = ev α K' := by
      intro α hα
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hα
      obtain ⟨a, ha, b, hb, hab, heq⟩ := hα
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_biUnion]
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact absurd rfl hab
      · exact Or.inr ⟨b, hb, heq⟩
      · exact Or.inr ⟨a, ha, heq.symm⟩
      · exact Or.inl ⟨a, ha, b, hb, hab, heq⟩
    refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
    refine add_le_add ih ((Finset.card_biUnion_le_card_mul _ _ 1 fun K' hK' => ?_).trans_eq
      (mul_one _))
    have hne : K ≠ K' := fun h => hK (h ▸ hK')
    exact card_filter_affine_eq_le_one hq (c := K.1) (d := K.2) (c' := K'.1) (d' := K'.2)
      (by simpa using hne)

/-- A table with `n` entries has two distinct keys that agree at no more than `n.choose 2`
points. -/
private theorem card_filter_collides_le (hq : q.Prime) [NeZero q] (tab : Tab q) :
    (Finset.univ.filter fun α : ZMod q => Collides α tab).card ≤ tab.length.choose 2 := by
  classical
  let s := (tab.map Prod.fst).toFinset
  have hsub : (Finset.univ.filter fun α : ZMod q => Collides α tab) ⊆
      Finset.univ.filter fun α : ZMod q => ∃ K ∈ s, ∃ K' ∈ s, K ≠ K' ∧ ev α K = ev α K' := by
    intro α hα
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hα ⊢
    obtain ⟨e, he, e', he', hne, heq⟩ := hα
    exact ⟨e.1, List.mem_toFinset.mpr (List.mem_map_of_mem he), e'.1,
      List.mem_toFinset.mpr (List.mem_map_of_mem he'), hne, heq⟩
  refine (Finset.card_le_card hsub).trans ((card_filter_pairs_le hq s).trans ?_)
  exact Nat.choose_le_choose 2 ((List.toFinset_card_le _).trans_eq (List.length_map _))

/-- **The core bound for deterministic adversaries.** -/
private theorem detGame_apply_le [NeZero q] (hq : q.Prime) {T : ℕ}
    {D : ZMod q → ZMod q → OracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)}
    (hD : ∀ g u, (D g u).IsQueryBounded T) :
    detGame D true ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0∞) / q := by
  rw [detGame_eq]
  set symRun := (OracleComp.interpret symOracle (primGame D)).run ([] : Tab q) with hsymRun
  have hlen : ∀ y ∈ symRun.support, y.2.length ≤ 3 * T + 2 := fun y hy => by
    simpa using (isQueryBounded_primGame hD).measure_le symOracle List.length
      (fun p s res s' h => length_le_of_mem_support_symOracle p s res s' h) (s := []) hy
  calc _ ≤ ((PMF.uniformOfFintype (ZMod q)).bind fun α =>
          symRun.bind fun y => PMF.pure (decide (y.1 = α))) true +
        ((PMF.uniformOfFintype (ZMod q)).bind fun α =>
          symRun.bind fun y => PMF.pure (decide (Collides α y.2))) true :=
        PMF.bind_apply_le_add_on_support _ true fun α _ => real_le α D
    _ ≤ (q : ℝ≥0∞)⁻¹ + ((3 * T + 2).choose 2 : ℝ≥0∞) * (q : ℝ≥0∞)⁻¹ := by
        rw [PMF.bind_comm, PMF.bind_comm (PMF.uniformOfFintype (ZMod q))]
        refine add_le_add (PMF.bind_apply_le_on_support _ fun y _ => ?_)
          (PMF.bind_apply_le_on_support _ fun y hy => ?_)
        · rw [PMF.uniformOfFintype_bind_decide_eq_apply_true, ZMod.card]
        · rw [bind_pure_decide_apply_true _ (fun α : ZMod q => Collides α y.2),
            PMF.toOuterMeasure_uniformOfFintype, ZMod.card]
          gcongr
          exact_mod_cast (card_filter_collides_le hq y.2).trans (Nat.choose_le_choose 2 (hlen y hy))
    _ = _ := by
        rw [ENNReal.div_eq_inv_mul]
        push_cast
        ring

/-- The replies of the group oracle on labels in `ZMod q` form a finite type. -/
private instance [NeZero q] (query : GroupQuery q (ZMod q)) :
    Fintype (GroupOracleSpec q (ZMod q) query) := by
  cases query
  · exact inferInstanceAs (Fintype (ZMod q))
  · exact inferInstanceAs (Fintype (Option (ZMod q)))

/-- Fixing the adversary's coins for each pair of inputs makes the game an average of games against
deterministic adversaries. -/
private theorem permDlogGame_eq_bind_detGame [NeZero q]
    (A : ZMod q → ZMod q → ProbOracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)) :
    permDlogGame A =
      (Probability.PMF.pi fun gu : ZMod q × ZMod q => ProbOracleComp.coinLaw (A gu.1 gu.2)).bind
        fun Ω => detGame fun g u => ProbOracleComp.fixCoins (A g u) (Ω (g, u)) := by
  have key (σ : Equiv.Perm (ZMod q)) (g u : ZMod q) :
      runLabeled (σ : ZMod q → ZMod q) (A g u) =
        (Probability.PMF.pi fun gu : ZMod q × ZMod q =>
          ProbOracleComp.coinLaw (A gu.1 gu.2)).bind fun Ω =>
            OracleComp.interpret (fun query => PMF.pure (answer σ query))
              (ProbOracleComp.fixCoins (A g u) (Ω (g, u))) := by
    have hpi : (Probability.PMF.pi fun gu : ZMod q × ZMod q =>
        ProbOracleComp.coinLaw (A gu.1 gu.2)).map (fun Ω => Ω (g, u)) =
          ProbOracleComp.coinLaw (A g u) :=
      Probability.PMF.pi_map_eval _ (g, u)
    unfold runLabeled
    rw [← ProbOracleComp.bind_interpret_fixCoins (A g u) (answer σ), ← hpi, PMF.bind_map]
    rfl
  unfold permDlogGame detGame
  simp only [Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure, key,
    PMF.bind_bind]
  simp_rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod q))]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Equiv.Perm (ZMod q)))]

/-! ### Bijective labels -/

/-- The core of the proof: Theorem 16.3 for labels in `ZMod q` and a uniform permutation as
labeling. -/
private theorem succProbability_permDlogGame_le [NeZero q] (hq : q.Prime) {T : ℕ}
    {A : ZMod q → ZMod q → ProbOracleComp (GroupOracleSpec q (ZMod q)) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (permDlogGame A).succProbability ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q := by
  have h : permDlogGame A true ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0∞) / q := by
    rw [permDlogGame_eq_bind_detGame]
    exact PMF.bind_apply_le_on_support _ fun Ω _ =>
      detGame_apply_le hq fun g u => ProbOracleComp.isQueryBounded_fixCoins (hA g u) _
  refine (ENNReal.toNNReal_mono (ENNReal.div_ne_top (ENNReal.natCast_ne_top _)
    (Nat.cast_ne_zero.mpr (NeZero.ne q))) h).trans_eq ?_
  rw [ENNReal.toNNReal_div, ENNReal.toNNReal_natCast, ENNReal.toNNReal_natCast]

/-! ### Theorem 16.3 -/

/-- **Theorem 16.3, sharp form.** For prime `q` and an adversary that makes at most `T` queries to
the group oracle on every path, the discrete-logarithm game in the generic group model is won with
probability at most `((3T + 2).choose 2 + 1) / q`. This is the bound the proof of
[BonehShoup2023], Theorem 16.3, gives before it rounds `(3T + 2).choose 2` up to `(3T + 2)² / 2`. -/
theorem succProbability_dlogGame_le_choose [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ (((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q := by
  rw [dlogGame_eq_bind_permDlogGame]
  have hb := PMF.bind_apply_le_on_support (PMF.uniformOfFintype (ZMod q ↪ S))
    (f := fun j => permDlogGame fun g u => relabel j (A (j g) (j u))) (b := true)
    (c := (((((3 * T + 2).choose 2 + 1 : ℕ) : ℝ≥0) / q : ℝ≥0) : ℝ≥0∞)) fun j _ => by
      have h := succProbability_permDlogGame_le hq (T := T)
        (A := fun g u => relabel j (A (j g) (j u))) fun g u => isQueryBounded_relabel j (hA _ _)
      calc (permDlogGame fun g u => relabel j (A (j g) (j u))) true
          = (((permDlogGame fun g u => relabel j (A (j g) (j u))) true).toNNReal : ℝ≥0∞) :=
            (ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)).symm
        _ ≤ _ := ENNReal.coe_le_coe.mpr h
  exact (ENNReal.toNNReal_mono ENNReal.coe_ne_top hb).trans_eq (ENNReal.toNNReal_coe _)

/-- **Theorem 16.3** ([BonehShoup2023], p. 693, eq. (16.6)). For prime `q` and an adversary that
makes at most `T` queries to the group oracle on every path, the discrete-logarithm game in the
generic group model is won with probability at most `((3T + 2)² / 2 + 1) / q`. -/
theorem succProbability_dlogGame_le [NeZero q] [Fintype S] [Nonempty (ZMod q ↪ S)]
    (hq : q.Prime) {T : ℕ} {A : S → S → ProbOracleComp (GroupOracleSpec q S) (ZMod q)}
    (hA : ∀ g u, (A g u).IsQueryBounded T) :
    (dlogGame A).succProbability ≤ ((3 * T + 2 : ℝ≥0) ^ 2 / 2 + 1) / q := by
  refine (succProbability_dlogGame_le_choose hq hA).trans ?_
  gcongr
  have h : ((3 * T + 2).choose 2 : ℝ≥0) ≤ (3 * T + 2 : ℝ≥0) ^ 2 / 2 := by
    rw [le_div_iff₀ (by norm_num)]
    have h2 : (3 * T + 2).choose 2 * 2 ≤ (3 * T + 2) ^ 2 := by
      rw [Nat.choose_two_right]
      calc (3 * T + 2) * (3 * T + 2 - 1) / 2 * 2 ≤ (3 * T + 2) * (3 * T + 2 - 1) :=
            Nat.div_mul_le_self _ _
        _ ≤ (3 * T + 2) ^ 2 := by
            rw [sq]; exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    exact_mod_cast h2
  push_cast
  exact add_le_add_left h 1

end Cslib.Crypto.GenericGroup
