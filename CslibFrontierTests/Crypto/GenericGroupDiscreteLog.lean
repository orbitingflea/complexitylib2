/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GenericGroup.DiscreteLog
import Mathlib.Tactic.NormNum.Prime

/-!
# The generic-group bound for discrete logarithm: an ordinary client

Uses the public API of `CslibFrontier.Crypto.Computational.GenericGroup.Relabel` and
`CslibFrontier.Crypto.Computational.GenericGroup.DiscreteLog` through ordinary imports:

* the sharp bound for the adversary of `ZMod 5` that makes no query and guesses `1` when its two
  labels agree: success probability at most `2 / 5`;
* both forms of the bound for an adversary that makes one query, with labels in `Fin 128` for a
  group of order `101`: at most `11 / 101` and at most `27 / 202`;
* relabelling a one-query program through `ZMod 5 ↪ Fin 8`: its query bound, and its run against a
  permutation `σ`;
* `Nonempty (ZMod q ↪ S)` is the book's `|S| ≥ q`;
* primality is needed where the proof uses it: in `ZMod 4` the distinct linear forms `2 X` and `0`
  agree at two points.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupDiscreteLog

open Cslib Cslib.Crypto.GenericGroup
open scoped NNReal

/-! ### An adversary without queries -/

/-- Guess `1` when the generator and the challenge have the same label, `0` otherwise; no query. -/
private def guess (g u : ZMod 5) : ProbOracleComp (GroupOracleSpec 5 (ZMod 5)) (ZMod 5) :=
  pure (if g = u then 1 else 0)

private instance : Nonempty (ZMod 5 ↪ ZMod 5) := ⟨Function.Embedding.refl _⟩

example : (dlogGame guess).succProbability ≤ 2 / 5 := by
  refine (succProbability_dlogGame_le_choose (T := 0) Nat.prime_five
    fun g u => OracleComp.IsCostBounded.pure _ 0).trans_eq ?_
  norm_num [Nat.choose_self]

/-! ### A querying adversary with more labels than group elements -/

/-- With labels in `Fin 128` for a group of order `101`, ask for the label of `u ^ 2 * g ^ 3` and
guess `100`, the solution of `2 * α + 3 = 1`, when the answer is the generator's label; one
query. -/
private def adv (g u : Fin 128) : ProbOracleComp (GroupOracleSpec 101 (Fin 128)) (ZMod 101) := do
  let r ← ProbOracleComp.query (spec := GroupOracleSpec 101 (Fin 128)) (.op u g 2 3)
  pure (if r = some g then 100 else 0)

private theorem adv_bounded (g u : Fin 128) : (adv g u).IsQueryBounded 1 :=
  ((ProbOracleComp.IsQueryBounded.query _).bind fun _ => OracleComp.IsCostBounded.pure _ 0).mono
    (by norm_num)

private instance : Nonempty (ZMod 101 ↪ Fin 128) :=
  Function.Embedding.nonempty_iff_card_le.mpr (by simp [ZMod.card])

example : (dlogGame adv).succProbability ≤ 11 / 101 := by
  refine (succProbability_dlogGame_le_choose (T := 1) (by norm_num) adv_bounded).trans_eq ?_
  norm_num [Nat.choose]

example : (dlogGame adv).succProbability ≤ 27 / 202 := by
  refine (succProbability_dlogGame_le (T := 1) (by norm_num) adv_bounded).trans_eq ?_
  norm_num

/-! ### Relabelling a concrete program -/

example (j : ZMod 5 ↪ Fin 8) :
    (relabel j
      (ProbOracleComp.query (spec := GroupOracleSpec 5 (Fin 8)) (.label 2))).IsQueryBounded 1 :=
  isQueryBounded_relabel j (ProbOracleComp.IsQueryBounded.query _)

example (j : ZMod 5 ↪ Fin 8) (σ : Equiv.Perm (ZMod 5)) :
    runLabeled (σ : ZMod 5 → ZMod 5)
        (relabel j (ProbOracleComp.query (spec := GroupOracleSpec 5 (Fin 8)) (.label 2))) =
      runLabeled (fun β => j (σ β))
        (ProbOracleComp.query (spec := GroupOracleSpec 5 (Fin 8)) (.label 2)) :=
  runLabeled_relabel j σ _

/-! ### Hypotheses -/

/-- An injective labeling exists exactly when `S` has at least `q` elements. -/
example (q : ℕ) [NeZero q] {S : Type} [Fintype S] : Nonempty (ZMod q ↪ S) ↔ q ≤ Fintype.card S := by
  rw [Function.Embedding.nonempty_iff_card_le, ZMod.card]

/-- Over `ZMod 4` the distinct forms `2 X + 0` and `0 X + 0` agree at `0` and `2`; the proof of
the bound needs `q` prime exactly here. -/
example : (Finset.univ.filter fun α : ZMod 4 => 2 * α + 0 = 0 * α + 0).card = 2 := by
  decide

end CslibFrontierTests.Crypto.GenericGroupDiscreteLog
