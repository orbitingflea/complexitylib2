/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.DecisionTree.CoordinateCap
public import CslibFrontier.Computability.QueryComplexity.Randomized
public import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Capped adaptive direct products

Let `J` index independent inputs. For each `j`, suppose every decision tree of depth at most
`c j` has weighted success at most `b j` on input `j`. A tree that may interleave its queries
to the inputs adaptively, but queries input `j` at most `c j` times on every path, outputs all
answers correctly with weighted success at most `∏ j, b j`. With `r` copies of one problem,
cap `L` and bound `b`, this is the bound `b ^ r` of [OpenAI2026Quartic, Lemma 4.1].

Each input may have its own partial function, weight, cap and bound; the query positions and
the finite, nonempty output alphabet are shared. A partial function takes values in
`Option β`, and an input mapped to `none` never counts as a success. Weights need only be
nonnegative; for probabilities, take normalised weights supported on the promise. The caps are
the structural caps `DecisionTree.Capped`. Neither a total budget of `∑ j, c j` queries nor a
bound on the expected number of queries to each input suffices; the test module checks a
counterexample to each.

Randomized algorithms are handled by averaging over a finitely supported law of trees
(`StdSimplex`, or `RandomizedDecisionTree`), each of which respects the caps. No definition of
promise randomized complexity is introduced.

The proof follows the induction in Will Cook's Lean formalization `quartic-query-lean`
(revision `db3feec`), which replaces the supermartingale argument of the source. The best
success of a depth-`c` tree for one input is a finite recursive optimum, attained by a tree.
Induction on the joint tree then updates one input's weight and spends one unit of its cap at
each query, so adaptive interleaving needs no conditioning or division.

## Main definitions

* `Cslib.DecisionTree.weightedSuccess`: success with nonnegative, possibly unnormalised weights.
* `Cslib.DecisionTree.productSuccess`: simultaneous success with independent coordinate weights.

## Main results

* `Cslib.DecisionTree.productSuccess_le_prod`: the capped direct product theorem.
* `Cslib.DecisionTree.sum_mul_productSuccess_le_prod`: the same bound averaged over independent,
  finitely supported side information.
* `Cslib.RandomizedDecisionTree.sum_mul_productSuccess_le_prod`: the same bound for the library's
  randomized decision trees.
* `Cslib.DecisionTree.productSuccess_le_prod_of_depth_le`,
  `Cslib.RandomizedDecisionTree.sum_mul_productSuccess_le_prod_of_depth_le`: a total depth bound
  no larger than every cap is sufficient.

## References

* [OpenAI, *A Nearly Quartic Separation Between Randomized and Quantum Query Complexity*,
  Lemma 4.1][OpenAI2026Quartic]
-/

public section

namespace Cslib.DecisionTree

open Finset Convexity

variable {ι β : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β]

/-- The weighted mass of inputs on which `t` returns the promised answer. Inputs where `f` is
`none` contribute zero. No normalisation or sign condition is part of this definition. -/
@[expose] def weightedSuccess (t : DecisionTree ι β) (ν : (ι → Bool) → ℝ)
    (f : (ι → Bool) → Option β) : ℝ :=
  ∑ x, ν x * if f x = some (t.eval x) then 1 else 0

/-- Restrict a weight to inputs whose queried bit has the given value. -/
private def restrictWeight (ν : (ι → Bool) → ℝ) (q : ι) (b : Bool) : (ι → Bool) → ℝ :=
  fun x => if x q = b then ν x else 0

/-- Weighted success is nonnegative for nonnegative weights. -/
theorem weightedSuccess_nonneg (t : DecisionTree ι β) (f : (ι → Bool) → Option β)
    {ν : (ι → Bool) → ℝ} (hν : ∀ x, 0 ≤ ν x) : 0 ≤ t.weightedSuccess ν f :=
  sum_nonneg fun x _ => mul_nonneg (hν x) (ite_nonneg zero_le_one le_rfl)

omit [Fintype ι] [DecidableEq ι] in
private theorem restrictWeight_nonneg {ν : (ι → Bool) → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (q : ι) (b : Bool) : ∀ x, 0 ≤ restrictWeight ν q b x := by
  intro x
  exact ite_nonneg (hν x) le_rfl

private theorem weightedSuccess_node (f : (ι → Bool) → Option β) (ν : (ι → Bool) → ℝ)
    (q : ι) (t₀ t₁ : DecisionTree ι β) :
    (node q t₀ t₁).weightedSuccess ν f =
      t₀.weightedSuccess (restrictWeight ν q false) f +
        t₁.weightedSuccess (restrictWeight ν q true) f := by
  unfold weightedSuccess restrictWeight
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  cases hx : x q <;> simp [eval_node, hx]

section Budget

variable [Fintype β] [Nonempty β]

/-- A private dynamic programme for the best weighted success at a fixed query budget. -/
private noncomputable def budgetValue (f : (ι → Bool) → Option β) :
    ℕ → ((ι → Bool) → ℝ) → ℝ
  | 0, ν => (univ : Finset β).sup' univ_nonempty fun b => (leaf b).weightedSuccess ν f
  | c + 1, ν => (univ : Finset (Option ι)).sup' ⟨none, mem_univ _⟩ fun o =>
      match o with
      | none => budgetValue f c ν
      | some q => budgetValue f c (restrictWeight ν q false) +
          budgetValue f c (restrictWeight ν q true)

private theorem budgetValue_le_succ (f : (ι → Bool) → Option β) (c : ℕ)
    (ν : (ι → Bool) → ℝ) : budgetValue f c ν ≤ budgetValue f (c + 1) ν := by
  rw [budgetValue]
  exact le_sup' (f := fun o : Option ι => match o with
    | none => budgetValue f c ν
    | some q => budgetValue f c (restrictWeight ν q false) +
        budgetValue f c (restrictWeight ν q true)) (mem_univ none)

private theorem budgetValue_add_le (f : (ι → Bool) → Option β) (c : ℕ)
    (ν : (ι → Bool) → ℝ) (q : ι) :
    budgetValue f c (restrictWeight ν q false) + budgetValue f c (restrictWeight ν q true)
      ≤ budgetValue f (c + 1) ν := by
  rw [budgetValue]
  exact le_sup' (f := fun o : Option ι => match o with
    | none => budgetValue f c ν
    | some q => budgetValue f c (restrictWeight ν q false) +
        budgetValue f c (restrictWeight ν q true)) (mem_univ (some q))

private theorem budgetValue_mono (f : (ι → Bool) → Option β) {c d : ℕ} (h : c ≤ d)
    (ν : (ι → Bool) → ℝ) : budgetValue f c ν ≤ budgetValue f d ν := by
  induction d, h using Nat.le_induction with
  | base => exact le_rfl
  | succ d _ ih => exact ih.trans (budgetValue_le_succ f d ν)

private theorem leafSuccess_le_budgetValue (f : (ι → Bool) → Option β) (c : ℕ)
    (ν : (ι → Bool) → ℝ) (b : β) : (leaf b).weightedSuccess ν f ≤ budgetValue f c ν := by
  refine le_trans ?_ (budgetValue_mono f (Nat.zero_le c) ν)
  exact le_sup' (f := fun b : β => (leaf b).weightedSuccess ν f) (mem_univ b)

private theorem budgetValue_nonneg (f : (ι → Bool) → Option β) (c : ℕ)
    {ν : (ι → Bool) → ℝ} (hν : ∀ x, 0 ≤ ν x) : 0 ≤ budgetValue f c ν := by
  obtain ⟨b⟩ := ‹Nonempty β›
  exact (weightedSuccess_nonneg (leaf b) f hν).trans (leafSuccess_le_budgetValue f c ν b)

/-- The finite recursion is attained by a tree. -/
private theorem exists_tree_budgetValue_le (f : (ι → Bool) → Option β) (c : ℕ)
    (ν : (ι → Bool) → ℝ) :
    ∃ t : DecisionTree ι β, t.depth ≤ c ∧ budgetValue f c ν ≤ t.weightedSuccess ν f := by
  induction c generalizing ν with
  | zero =>
    obtain ⟨b, -, hb⟩ := exists_mem_eq_sup' (s := (univ : Finset β)) univ_nonempty
      (fun b => (leaf b).weightedSuccess ν f)
    exact ⟨leaf b, le_rfl, by simpa only [budgetValue] using hb.le⟩
  | succ c ih =>
    rw [budgetValue]
    obtain ⟨o, -, ho⟩ := exists_mem_eq_sup' (s := (univ : Finset (Option ι)))
      ⟨none, mem_univ _⟩ (fun o => match o with
        | none => budgetValue f c ν
        | some q => budgetValue f c (restrictWeight ν q false) +
            budgetValue f c (restrictWeight ν q true))
    rw [ho]
    cases o with
    | none =>
      obtain ⟨t, ht, h⟩ := ih ν
      exact ⟨t, ht.trans (Nat.le_succ _), h⟩
    | some q =>
      obtain ⟨t₀, ht₀, h₀⟩ := ih (restrictWeight ν q false)
      obtain ⟨t₁, ht₁, h₁⟩ := ih (restrictWeight ν q true)
      refine ⟨node q t₀ t₁, ?_, ?_⟩
      · simp only [depth_node]
        omega
      · rw [weightedSuccess_node]
        exact add_le_add h₀ h₁

private theorem budgetValue_le_of_forall {f : (ι → Bool) → Option β} {c : ℕ}
    {ν : (ι → Bool) → ℝ} {b : ℝ}
    (h : ∀ t : DecisionTree ι β, t.depth ≤ c → t.weightedSuccess ν f ≤ b) :
    budgetValue f c ν ≤ b := by
  obtain ⟨t, ht, hle⟩ := exists_tree_budgetValue_le f c ν
  exact hle.trans (h t ht)

end Budget

variable {J : Type*} [Fintype J] [DecidableEq J]

/-- The weighted mass of independent inputs for which every coordinate of the output is
correct. Each coordinate has its own partial function and weight. -/
@[expose] def productSuccess (t : DecisionTree (J × ι) (J → β))
    (ν : J → (ι → Bool) → ℝ) (f : J → (ι → Bool) → Option β) : ℝ :=
  ∑ U : J → ι → Bool, (∏ j, ν j (U j)) *
    if ∀ j, f j (U j) = some (t.eval (Function.uncurry U) j) then 1 else 0

/-- A fixed vector of answers succeeds independently in each coordinate. -/
theorem productSuccess_leaf (ν : J → (ι → Bool) → ℝ)
    (f : J → (ι → Bool) → Option β) (s : J → β) :
    (leaf s).productSuccess ν f = ∏ j, (leaf (s j)).weightedSuccess (ν j) (f j) := by
  unfold productSuccess weightedSuccess
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun U _ => ?_
  simp only [eval_leaf, prod_mul_distrib]
  congr 1
  exact (Fintype.prod_boole (p := fun j => f j (U j) = some (s j))).symm

private theorem productSuccess_node (f : J → (ι → Bool) → Option β)
    (ν : J → (ι → Bool) → ℝ) (h : J) (q : ι)
    (t₀ t₁ : DecisionTree (J × ι) (J → β)) :
    (node (h, q) t₀ t₁).productSuccess ν f =
      t₀.productSuccess (Function.update ν h (restrictWeight (ν h) q false)) f +
        t₁.productSuccess (Function.update ν h (restrictWeight (ν h) q true)) f := by
  unfold productSuccess
  rw [← sum_add_distrib]
  refine sum_congr rfl fun U _ => ?_
  have hsplit : ∀ b, ∏ j, Function.update ν h (restrictWeight (ν h) q b) j (U j) =
      (if U h q = b then 1 else 0) * ∏ j, ν j (U j) := by
    intro b
    simp_rw [Function.apply_update (fun j w => w (U j)) ν h (restrictWeight (ν h) q b)]
    rw [prod_update_of_mem (mem_univ h), sdiff_singleton_eq_erase,
      ← mul_prod_erase univ (fun j => ν j (U j)) (mem_univ h)]
    unfold restrictWeight
    split_ifs <;> simp
  rw [hsplit, hsplit]
  cases hq : U h q <;> simp [eval_node, Function.uncurry, hq]

section DirectProduct

variable [Fintype β] [Nonempty β]

private theorem productSuccess_le_prod_budgetValue (f : J → (ι → Bool) → Option β)
    (t : DecisionTree (J × ι) (J → β)) (ν : J → (ι → Bool) → ℝ) (c : J → ℕ)
    (hν : ∀ j x, 0 ≤ ν j x) (ht : t.Capped c) :
    t.productSuccess ν f ≤ ∏ j, budgetValue (f j) (c j) (ν j) := by
  induction t generalizing ν c with
  | leaf s =>
    rw [productSuccess_leaf]
    exact prod_le_prod₀ (fun j _ => weightedSuccess_nonneg (leaf (s j)) (f j) (hν j))
      fun j _ => leafSuccess_le_budgetValue (f j) (c j) (ν j) (s j)
  | node p t₀ t₁ ih₀ ih₁ =>
    obtain ⟨h, q⟩ := p
    obtain ⟨h0, h₀, h₁⟩ := capped_node_iff.mp ht
    have hν' : ∀ b j x, 0 ≤ Function.update ν h (restrictWeight (ν h) q b) j x := by
      intro b j x
      by_cases hj : j = h
      · subst hj
        simpa using restrictWeight_nonneg (hν j) q b x
      · simpa [Function.update_of_ne hj] using hν j x
    let c' := Function.update c h (c h - 1)
    have hprod : ∀ b, ∏ j, budgetValue (f j) (c' j)
          (Function.update ν h (restrictWeight (ν h) q b) j) =
        budgetValue (f h) (c h - 1) (restrictWeight (ν h) q b) *
          ∏ j ∈ univ.erase h, budgetValue (f j) (c j) (ν j) := by
      intro b
      dsimp only [c']
      simp_rw [Function.apply_update₂ (fun j n w => budgetValue (f j) n w)
        c ν h (c h - 1) (restrictWeight (ν h) q b)]
      rw [prod_update_of_mem (mem_univ h), sdiff_singleton_eq_erase]
    have hP : 0 ≤ ∏ j ∈ univ.erase h, budgetValue (f j) (c j) (ν j) :=
      prod_nonneg fun j _ => budgetValue_nonneg (f j) (c j) (hν j)
    rw [productSuccess_node]
    calc _ ≤ _ := add_le_add (ih₀ _ c' (hν' false) h₀) (ih₁ _ c' (hν' true) h₁)
      _ = (budgetValue (f h) (c h - 1) (restrictWeight (ν h) q false) +
            budgetValue (f h) (c h - 1) (restrictWeight (ν h) q true)) *
          ∏ j ∈ univ.erase h, budgetValue (f j) (c j) (ν j) := by
            rw [hprod, hprod, add_mul]
      _ ≤ budgetValue (f h) (c h) (ν h) *
          ∏ j ∈ univ.erase h, budgetValue (f j) (c j) (ν j) := by
            refine mul_le_mul_of_nonneg_right ?_ hP
            have hstep := budgetValue_add_le (f h) (c h - 1) (ν h) q
            rwa [Nat.sub_add_cancel h0] at hstep
      _ = ∏ j, budgetValue (f j) (c j) (ν j) :=
        mul_prod_erase univ (fun j => budgetValue (f j) (c j) (ν j)) (mem_univ h)

end DirectProduct

section DirectProductTheorems

variable [Finite β] [Nonempty β]

/-- **Capped direct product theorem** [OpenAI2026Quartic, Lemma 4.1], for deterministic trees,
with possibly different partial functions, weights, caps and bounds for the inputs. If every
tree of depth at most `c j` has weighted success at most `b j` on input `j`, then every tree
that queries input `j` at most `c j` times on each path, interleaving its queries adaptively,
answers all inputs correctly with weighted success at most `∏ j, b j`. -/
theorem productSuccess_le_prod {f : J → (ι → Bool) → Option β} {ν : J → (ι → Bool) → ℝ}
    {c : J → ℕ} {b : J → ℝ} (hν : ∀ j x, 0 ≤ ν j x)
    (hb : ∀ j (t : DecisionTree ι β), t.depth ≤ c j → t.weightedSuccess (ν j) (f j) ≤ b j)
    (t : DecisionTree (J × ι) (J → β)) (ht : t.Capped c) :
    t.productSuccess ν f ≤ ∏ j, b j := by
  let := Fintype.ofFinite β
  refine (productSuccess_le_prod_budgetValue f t ν c hν ht).trans ?_
  exact prod_le_prod₀ (fun j _ => budgetValue_nonneg (f j) (c j) (hν j))
    fun j _ => budgetValue_le_of_forall (hb j)

/-- The capped direct product bound after drawing side information `s`, independent of the
inputs, from a finitely supported probability distribution `p` and running the tree `T s`.
The caps are required only for seeds in the support of `p`. -/
theorem sum_mul_productSuccess_le_prod {S : Type*} {f : J → (ι → Bool) → Option β}
    {ν : J → (ι → Bool) → ℝ} {c : J → ℕ} {b : J → ℝ}
    (hν : ∀ j x, 0 ≤ ν j x)
    (hb : ∀ j (t : DecisionTree ι β), t.depth ≤ c j → t.weightedSuccess (ν j) (f j) ≤ b j)
    (p : StdSimplex ℝ S) (T : S → DecisionTree (J × ι) (J → β))
    (hT : ∀ s ∈ p.weights.support, (T s).Capped c) :
    (p.weights.sum fun s w => w * (T s).productSuccess ν f) ≤ ∏ j, b j :=
  StdSimplex.sum_mul_le_of_forall_le fun s hs => productSuccess_le_prod hν hb (T s) (hT s hs)

/-- A total depth bound `d` suffices for the capped direct product bound when `d ≤ c j` for
every input `j`. -/
theorem productSuccess_le_prod_of_depth_le {f : J → (ι → Bool) → Option β}
    {ν : J → (ι → Bool) → ℝ} {c : J → ℕ} {b : J → ℝ} {d : ℕ}
    (hν : ∀ j x, 0 ≤ ν j x)
    (hb : ∀ j (t : DecisionTree ι β), t.depth ≤ c j → t.weightedSuccess (ν j) (f j) ≤ b j)
    (t : DecisionTree (J × ι) (J → β)) (ht : t.depth ≤ d) (hc : ∀ j, d ≤ c j) :
    t.productSuccess ν f ≤ ∏ j, b j :=
  productSuccess_le_prod hν hb t (capped_of_depth_le ht hc)

end DirectProductTheorems

end Cslib.DecisionTree

namespace Cslib.RandomizedDecisionTree

variable {ι β J : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq β] [Finite β] [Nonempty β]
  [Fintype J] [DecidableEq J]

/-- The capped direct product bound for a randomized decision tree `μ`: the average over the
drawn tree of its simultaneous success is at most `∏ j, b j`. Every tree that `μ` can draw must
respect the caps, so the caps hold in the worst case over the coins. -/
theorem sum_mul_productSuccess_le_prod {f : J → (ι → Bool) → Option β}
    {ν : J → (ι → Bool) → ℝ} {c : J → ℕ} {b : J → ℝ}
    (hν : ∀ j x, 0 ≤ ν j x)
    (hb : ∀ j (t : DecisionTree ι β), t.depth ≤ c j → t.weightedSuccess (ν j) (f j) ≤ b j)
    (μ : RandomizedDecisionTree (J × ι) (J → β))
    (hμ : ∀ t ∈ μ.weights.support, t.Capped c) :
    (μ.weights.sum fun t w => w * t.productSuccess ν f) ≤ ∏ j, b j :=
  DecisionTree.sum_mul_productSuccess_le_prod hν hb μ id hμ

/-- The randomized capped direct product bound under a bound `d ≤ c j` on the depth of `μ`,
the largest depth of a tree it can draw. -/
theorem sum_mul_productSuccess_le_prod_of_depth_le {f : J → (ι → Bool) → Option β}
    {ν : J → (ι → Bool) → ℝ} {c : J → ℕ} {b : J → ℝ} {d : ℕ}
    (hν : ∀ j x, 0 ≤ ν j x)
    (hb : ∀ j (t : DecisionTree ι β), t.depth ≤ c j → t.weightedSuccess (ν j) (f j) ≤ b j)
    (μ : RandomizedDecisionTree (J × ι) (J → β)) (hμ : μ.depth ≤ d)
    (hc : ∀ j, d ≤ c j) :
    (μ.weights.sum fun t w => w * t.productSuccess ν f) ≤ ∏ j, b j :=
  sum_mul_productSuccess_le_prod hν hb μ fun _ ht =>
    DecisionTree.capped_of_depth_le ((depth_le_depth ht).trans hμ) hc

end Cslib.RandomizedDecisionTree
