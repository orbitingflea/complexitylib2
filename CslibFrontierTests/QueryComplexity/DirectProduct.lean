/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.QueryComplexity.DirectProduct
import CslibFrontier.Computability.QueryComplexity.Randomized.ZeroError
import Mathlib.Tactic.NormNum

/-!
# Concrete tests for capped adaptive direct products

All tests use two independent copies of two-bit parity under the uniform distribution. Every
tree of depth at most one succeeds with probability `1/2` on one copy.

* With one query per copy, reading one bit of each copy and guessing succeeds on both copies
  with probability exactly `1/4 = (1/2)^2`, so the bound of `productSuccess_le_prod` is attained.
* A total budget of two queries does not suffice: reading both bits of the first copy and
  guessing the second succeeds with probability `1/2`.
* A cap on the expected number of queries to each copy does not suffice: a fair coin that
  chooses between reading all four bits and guessing both answers makes one query to each copy
  in expectation on every input, and succeeds with probability `5/8`.

The tests also cover a violated cap, off-promise mass, the empty product, and a randomized
law. Ordinary imports exercise the public API and exposed definitions.
-/

-- This test driver deliberately exports no API.
set_option linter.privateModule false

namespace CslibFrontierTests.QueryComplexity.DirectProduct

open Cslib Cslib.DecisionTree Convexity Finset

private def parity₂ (x : Bool → Bool) : Option Bool := some (x false ^^ x true)

private noncomputable def uniform₂ (_ : Bool → Bool) : ℝ := 1 / 4

private theorem shallow_count (t : DecisionTree Bool Bool) (ht : t.depth ≤ 1) :
    (∑ x : Bool → Bool, if parity₂ x = some (t.eval x) then 1 else 0 : ℕ) = 2 := by
  cases t with
  | leaf b =>
    have h : ∀ b : Bool,
        (∑ x : Bool → Bool, if parity₂ x = some b then 1 else 0 : ℕ) = 2 := by decide
    exact h b
  | node q left right =>
    cases left with
    | node i ll lr => simp only [depth_node] at ht; omega
    | leaf a =>
      cases right with
      | node i rl rr => simp only [depth_node, depth_leaf] at ht; omega
      | leaf b =>
        have h : ∀ q a b : Bool,
            (∑ x : Bool → Bool,
              if parity₂ x = some ((node q (leaf a) (leaf b)).eval x)
              then 1 else 0 : ℕ) = 2 := by decide
        exact h q a b

private theorem shallow_success (t : DecisionTree Bool Bool) (ht : t.depth ≤ 1) :
    t.weightedSuccess uniform₂ parity₂ = 1 / 2 := by
  have h : (∑ x : Bool → Bool,
      if parity₂ x = some (t.eval x) then 1 else 0 : ℝ) = 2 := by
    exact_mod_cast shallow_count t ht
  unfold weightedSuccess uniform₂
  rw [← mul_sum, h]
  norm_num

/-- `product_success t k` proves `t.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = v`
when `t` answers both copies correctly on exactly `k` of the sixteen input pairs and
`v = k / 16`. -/
local macro "product_success " t:term:max k:num : tactic => `(tactic| (
  have hn : (∑ U : Bool → Bool → Bool,
      if ∀ j, parity₂ (U j) = some (DecisionTree.eval $t (Function.uncurry U) j)
      then 1 else 0 : ℕ) = $k := by decide
  have hr : (∑ U : Bool → Bool → Bool,
      if ∀ j, parity₂ (U j) = some (DecisionTree.eval $t (Function.uncurry U) j)
      then 1 else 0 : ℝ) = $k := by exact_mod_cast hn
  unfold productSuccess uniform₂
  simp only [Fintype.prod_bool]
  rw [← mul_sum]
  calc
    _ = (1 / 4 * (1 / 4) : ℝ) * $k := by congr 1
    _ = _ := by norm_num))

/-! ## A tight instance -/

/-- Read one bit of each copy; guess that the unqueried bits are false. -/
private def guessBoth : DecisionTree (Bool × Bool) (Bool → Bool) :=
  node (false, false)
    (node (true, false) (leaf fun _ => false) (leaf fun j => j))
    (node (true, false) (leaf fun j => !j) (leaf fun _ => true))

private theorem guessBoth_capped : guessBoth.Capped (fun _ => 1) := by
  unfold Capped
  decide

private theorem guessBoth_success :
    guessBoth.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = 1 / 4 := by
  product_success guessBoth 4

/-- The quantified hardness hypothesis is satisfiable, and the product bound is attained. -/
private theorem parity_bound_tight :
    (∀ t : DecisionTree Bool Bool, t.depth ≤ 1 →
      t.weightedSuccess uniform₂ parity₂ ≤ 1 / 2) ∧
    guessBoth.Capped (fun _ => 1) ∧
    guessBoth.productSuccess (fun _ => uniform₂) (fun _ => parity₂) ≤ (1 / 2 : ℝ) ^ 2 ∧
    guessBoth.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = 1 / 4 ∧
    (1 / 4 : ℝ) < 1 := by
  refine ⟨fun t ht => (shallow_success t ht).le, guessBoth_capped, ?_,
    guessBoth_success, by norm_num⟩
  have h := productSuccess_le_prod (b := fun _ : Bool => (1 / 2 : ℝ))
    (fun _ _ => by norm_num [uniform₂])
    (fun _ t ht => (shallow_success t ht).le) guessBoth guessBoth_capped
  simpa [Fintype.prod_bool, pow_two] using h

/-! ## The caps cannot be weakened -/

/-- Read both bits of copy `j`, then continue with the two bits read. -/
private def readCopy (j : Bool) (k : Bool → Bool → DecisionTree (Bool × Bool) (Bool → Bool)) :
    DecisionTree (Bool × Bool) (Bool → Bool) :=
  node (j, false) (node (j, true) (k false false) (k false true))
    (node (j, true) (k true false) (k true true))

/-- Solve the first copy exactly and guess `false` for the second. -/
private def solveFirst : DecisionTree (Bool × Bool) (Bool → Bool) :=
  readCopy false fun a b => leaf fun j => !j && (a ^^ b)

/-- A total depth budget of `2 = 2 * 1` does not give the bound `(1/2)^2`: `solveFirst` uses
both queries on the first copy and succeeds with probability `1/2`. Separate caps are needed. -/
private theorem total_depth_budget_insufficient :
    (∀ t : DecisionTree Bool Bool, t.depth ≤ 1 →
      t.weightedSuccess uniform₂ parity₂ ≤ 1 / 2) ∧
    solveFirst.depth = 2 * 1 ∧ ¬ solveFirst.Capped (fun _ => 1) ∧
    solveFirst.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = 1 / 2 ∧
    (1 / 2 : ℝ) ^ 2 < solveFirst.productSuccess (fun _ => uniform₂) (fun _ => parity₂) := by
  have hs : solveFirst.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = 1 / 2 := by
    product_success solveFirst 8
  refine ⟨fun t ht => (shallow_success t ht).le, by decide, by unfold Capped; decide, hs, ?_⟩
  rw [hs]
  norm_num

/-- Solve both copies exactly, reading all four bits. -/
private def solveBoth : DecisionTree (Bool × Bool) (Bool → Bool) :=
  readCopy false fun a b => readCopy true fun c d => leaf fun j => cond j (c ^^ d) (a ^^ b)

/-- A fair coin. -/
private noncomputable def fairCoin : StdSimplex ℝ Bool where
  weights := Finsupp.equivFunOnFinite.symm fun _ => 1 / 2
  nonneg c := by simp
  total := by
    rw [Finsupp.sum_fintype _ _ fun _ => rfl]
    simp only [Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_bool]
    norm_num

/-- A fair coin chooses between solving both copies and guessing both answers. -/
private noncomputable def coin : RandomizedDecisionTree (Bool × Bool) (Bool → Bool) :=
  fairCoin.map fun c => cond c solveBoth (leaf fun _ => false)

/-- An average over `coin` is the mean of the two trees' values. -/
private theorem sum_coin (F : DecisionTree (Bool × Bool) (Bool → Bool) → ℝ) :
    (coin.weights.sum fun t w => w * F t) = (F (leaf fun _ => false) + F solveBoth) / 2 := by
  rw [coin, StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index (fun _ => zero_mul _) fun _ _ _ => add_mul _ _ _,
    Finsupp.sum_fintype _ _ fun _ => zero_mul _]
  simp only [fairCoin, Finsupp.coe_equivFunOnFinite_symm, Fintype.sum_bool, Bool.cond_true,
    Bool.cond_false]
  ring

/-- A cap on the expected number of queries to each copy does not give the bound `(1/2)^2`:
`coin` queries each copy once in expectation on every input, yet succeeds with probability
`5/8`. Its solving branch violates the structural caps. -/
private theorem expected_caps_insufficient :
    (∀ (j : Bool) (x : Bool × Bool → Bool),
      (coin.weights.sum fun t w =>
        w * (t.weightedCost (fun p => if p.1 = j then 1 else 0) x : ℝ)) = 1) ∧
    ¬ solveBoth.Capped (fun _ => 1) ∧
    (coin.weights.sum fun t w =>
      w * t.productSuccess (fun _ => uniform₂) (fun _ => parity₂)) = 5 / 8 ∧
    (1 / 2 : ℝ) ^ 2 < coin.weights.sum fun t w =>
      w * t.productSuccess (fun _ => uniform₂) (fun _ => parity₂) := by
  have hcost : ∀ (j : Bool) (x : Bool × Bool → Bool),
      solveBoth.weightedCost (fun p => if p.1 = j then 1 else 0) x = 2 := by decide
  have hsolve : solveBoth.productSuccess (fun _ => uniform₂) (fun _ => parity₂) = 1 := by
    product_success solveBoth 16
  have hguess : (leaf fun _ => false : DecisionTree (Bool × Bool) (Bool → Bool)).productSuccess
      (fun _ => uniform₂) (fun _ => parity₂) = 1 / 4 := by
    product_success (leaf fun _ => false : DecisionTree (Bool × Bool) (Bool → Bool)) 4
  have hs : (coin.weights.sum fun t w =>
      w * t.productSuccess (fun _ => uniform₂) (fun _ => parity₂)) = 5 / 8 := by
    rw [sum_coin, hsolve, hguess]
    norm_num
  refine ⟨fun j x => ?_, by unfold Capped; decide, hs, by rw [hs]; norm_num⟩
  rw [sum_coin, hcost j x, weightedCost_leaf]
  norm_num

/-! ## Further checks -/

/-- The cap condition rejects a second query to the same coordinate. -/
example : ¬ (node (false, true) guessBoth guessBoth).Capped (fun _ => 1) := by
  unfold Capped
  decide

/-- Out-of-promise input mass never counts as success. -/
example (t : DecisionTree Bool Bool) :
    t.weightedSuccess uniform₂ (fun _ => none) = 0 := by
  simp [weightedSuccess]

/-- No copies means success mass one, including when single-copy weights have mass zero. -/
example : (leaf (fun j : Fin 0 => Fin.elim0 j) :
      DecisionTree (Fin 0 × Bool) (Fin 0 → Bool)).productSuccess
      (fun _ _ => 0) (fun _ => parity₂) = 1 := by
  rw [productSuccess_leaf]
  simp

/-- The randomized form applies to a law on several trees that all respect the caps: a fair coin
choosing between `guessBoth` and guessing both answers without queries. -/
example : ((RandomizedDecisionTree.uniformMixture fun c => cond c guessBoth (leaf fun _ => false)
    ).weights.sum fun t w => w * t.productSuccess (fun _ => uniform₂) (fun _ => parity₂))
      ≤ (1 / 4 : ℝ) := by
  have h := RandomizedDecisionTree.sum_mul_productSuccess_le_prod (c := fun _ => 1)
    (b := fun _ : Bool => (1 / 2 : ℝ)) (fun _ _ => by norm_num [uniform₂])
    (fun _ t ht => (shallow_success t ht).le)
    (RandomizedDecisionTree.uniformMixture fun c => cond c guessBoth (leaf fun _ => false))
    (by
      intro t ht
      obtain ⟨c, rfl⟩ := RandomizedDecisionTree.exists_eq_of_mem_support_uniformMixture ht
      cases c
      · exact capped_leaf _ _
      · exact guessBoth_capped)
  norm_num [Fintype.prod_bool] at h ⊢
  exact h

end CslibFrontierTests.QueryComplexity.DirectProduct
