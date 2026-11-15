/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep

/-!
# The generic group oracle and baby-step/giant-step: an ordinary client

Uses the public API of `CslibFrontier.Crypto.Computational.GenericGroup.Basic` and
`CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep` through ordinary imports, in
`ZMod 11` with base point `1`, where `β • 1 = β`:

* the oracle of `ZMod 11` evaluates (its body is exposed) and is the generic group oracle of the
  labeling `β ↦ β • 1`;
* baby-step/giant-step at the book's table size `4 = ⌈11^(1/2)⌉` outputs the discrete logarithm,
  with at most `6 = 2 * Nat.sqrt 10` products, and so does brute force (`m = 11`, `n = 1`) with
  at most `10`;
* `(2 * Nat.sqrt (q - 1))^2 < 4 * q`, the comparison with the book's `2 q^(1/2)`.

`CslibFrontierTests/Crypto/GenericGroupRuns.lean` evaluates the programs themselves and shows that
the hypotheses are needed.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroup

open Cslib Cslib.Crypto.GenericGroup

/-! ### The oracle of `ZMod 11` -/

example : groupAnswer 11 (1 : ZMod 11) (.op 3 5 2 4) = some (2 * 3 + 4 * 5) := by decide

example : groupAnswer 11 (1 : ZMod 11) (.label 7) = 7 := by decide

private theorem surjective_smul_one : Function.Surjective fun β : ZMod 11 => β • (1 : ZMod 11) :=
  fun β => ⟨β, by simp⟩

private theorem injective_smul_one : Function.Injective fun β : ZMod 11 => β • (1 : ZMod 11) :=
  fun β₁ β₂ h => by simpa using h

example : groupAnswer 11 (1 : ZMod 11) = answer 11 (ZMod 11) fun β => β • 1 :=
  groupAnswer_eq_answer surjective_smul_one

example : answer 11 (ZMod 11) id (.op 3 5 2 4) = some 4 := by
  rw [show (3 : ZMod 11) = id 3 from rfl, show (5 : ZMod 11) = id 5 from rfl,
    answer_op_label Function.injective_id]
  decide

/-! ### Baby-step/giant-step in `ZMod 11` -/

example : (babyStepGiantStep 4 4 (1 : ZMod 11) 7).evalPure (groupAnswer 11 1) = 7 := by
  simpa using evalPure_groupAnswer_babyStepGiantStep injective_smul_one (m := 4) (n := 4)
    (by norm_num) 7

example (α : ZMod 11) :
    (babyStepGiantStep 4 4 (id 1) (id α)).evalPure (answer 11 (ZMod 11) id) = α ∧
      OracleComp.IsQueryBounded (babyStepGiantStep (q := 11) 4 4 (id 1) (id α)) 6 := by
  have h : Nat.sqrt 10 = 3 := Nat.sqrt_add_eq (a := 1) 3 (by norm_num)
  simpa only [h] using babyStepGiantStep_sqrt Function.injective_id α

example (g u : ZMod 11) :
    OracleComp.QueriesSatisfy GroupQuery.IsProduct (babyStepGiantStep (q := 11) 4 4 g u) ∧
      OracleComp.IsQueryBounded (babyStepGiantStep (q := 11) 4 4 g u) 6 :=
  ⟨queriesSatisfy_babyStepGiantStep 4 4 g u, isQueryBounded_babyStepGiantStep 4 4 g u⟩

/-- Brute force is the instance `m = 11`, `n = 1`, with at most `10` products. -/
example (α : ZMod 11) :
    (babyStepGiantStep 11 1 (1 : ZMod 11) (α • 1)).evalPure (groupAnswer 11 1) = α ∧
      OracleComp.IsQueryBounded (babyStepGiantStep (q := 11) 11 1 (1 : ZMod 11) (α • 1)) 10 :=
  ⟨evalPure_groupAnswer_babyStepGiantStep injective_smul_one (by norm_num) α,
    isQueryBounded_babyStepGiantStep 11 1 1 _⟩

/-- At the book's table size `Nat.sqrt (q - 1) + 1`, the product count `2 * Nat.sqrt (q - 1)` is
less than `2 * q^(1/2)`. -/
example (q : ℕ) (hq : 0 < q) : (2 * Nat.sqrt (q - 1)) ^ 2 < 4 * q := by
  have h := Nat.sqrt_le' (q - 1)
  have h₂ : (2 * Nat.sqrt (q - 1)) ^ 2 = 4 * Nat.sqrt (q - 1) ^ 2 := by ring
  omega

end CslibFrontierTests.Crypto.GenericGroup
