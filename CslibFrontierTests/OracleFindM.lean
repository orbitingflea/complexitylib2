/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Control.Monad.FindM
import CslibFrontier.Languages.Probabilistic.Traverse.FindM

/-! Clients of `List.findM?_cons`, `OracleComp.evalPure_findM?`,
`OracleComp.IsCostBounded.findM?`, and `OracleComp.QueriesSatisfy.findM?` under module
encapsulation. -/

namespace CslibFrontierTests.OracleFindM

open Cslib

/-- A search against a concrete oracle: the first `x` whose square is `9`. -/
example : OracleComp.evalPure (spec := fun _ : ℕ => ℕ) (fun n => n * n)
    ([1, 2, 3, 4].findM? fun x =>
      (fun y => decide (y = 9)) <$> OracleComp.query (spec := fun _ : ℕ => ℕ) x) = some 3 := by
  simp

/-- No element passes: the search returns `none`. -/
example : OracleComp.evalPure (spec := fun _ : ℕ => ℕ) (fun n => n * n)
    ([1, 2, 4].findM? fun x =>
      (fun y => decide (y = 9)) <$> OracleComp.query (spec := fun _ : ℕ => ℕ) x) = none := by
  simp

/-- Two elements pass (`6` and `9` are `0` modulo `3`): the search returns the first. -/
example : OracleComp.evalPure (spec := fun _ : ℕ => ℕ) (fun n => n % 3)
    ([4, 6, 5, 9].findM? fun x =>
      (fun y => decide (y = 0)) <$> OracleComp.query (spec := fun _ : ℕ => ℕ) x) = some 6 := by
  simp

/-- A test that makes two calls: the search costs at most `xs.length * 2`. -/
example (xs : List ℕ) :
    OracleComp.IsQueryBounded (spec := fun _ : ℕ => ℕ)
      (xs.findM? fun x => do
        let a ← OracleComp.query (spec := fun _ : ℕ => ℕ) x
        let b ← OracleComp.query (spec := fun _ : ℕ => ℕ) a
        return decide (b = 0)) (xs.length * 2) :=
  OracleComp.IsCostBounded.findM? fun x _ =>
    OracleComp.IsCostBounded.bind (cost := fun _ : ℕ => 1) (n := 1) (m := 1)
      (OracleComp.IsCostBounded.query x) fun a =>
        OracleComp.IsCostBounded.bind (cost := fun _ : ℕ => 1) (n := 1) (m := 0)
          (OracleComp.IsCostBounded.query a) fun _ => .pure _ 0

/-- A weighted cost: calls at even points are free, so a search over even points costs nothing. -/
example (xs : List ℕ) (h : ∀ x ∈ xs, x % 2 = 0) :
    OracleComp.IsCostBounded (spec := fun _ : ℕ => Bool) (fun q => q % 2)
      (xs.findM? fun x => OracleComp.query (spec := fun _ : ℕ => Bool) x) (xs.length * 0) :=
  OracleComp.IsCostBounded.findM? fun x hx => by
    have := OracleComp.IsCostBounded.query (spec := fun _ : ℕ => Bool) (cost := fun q => q % 2) x
    simpa [h x hx] using this

/-- The search stops at the first accepted element: a test that accepts every reply makes one
call, whatever the list. -/
example (a : ℕ) (as : List ℕ) :
    OracleComp.IsQueryBounded (spec := fun _ : ℕ => Bool)
      ((a :: as).findM? fun x => (fun _ => true) <$> OracleComp.query x) 1 := by
  rw [List.findM?_cons, bind_map_left]
  exact OracleComp.IsCostBounded.liftBind_iff.mpr ⟨le_rfl, fun _ => .pure _ _⟩

/-- The budget `xs.length * n` cannot be lowered in general: two candidates and a test that may
reject need two calls. -/
example : ¬ OracleComp.IsQueryBounded (spec := fun _ : ℕ => Bool)
    ([0, 1].findM? fun x => OracleComp.query x) 1 := by
  intro h
  simp only [List.findM?_cons] at h
  have h1 := (OracleComp.IsCostBounded.liftBind_iff.mp h).2 false
  exact absurd (OracleComp.IsCostBounded.liftBind_iff.mp h1).1 (by decide)

/-- The search calls the oracle only where its tests do. -/
example (xs : List ℕ) :
    OracleComp.QueriesSatisfy (spec := fun _ : ℕ => Bool) (fun q => q ∈ xs)
      (xs.findM? fun x => OracleComp.query (spec := fun _ : ℕ => Bool) x) :=
  OracleComp.QueriesSatisfy.findM? fun _ hx => OracleComp.QueriesSatisfy.query hx

/-- A predicate that one candidate's call violates does not hold of the search. -/
example : ¬ OracleComp.QueriesSatisfy (spec := fun _ : ℕ => Bool) (fun q => q ≠ 1)
    ([0, 1].findM? fun x => OracleComp.query x) := by
  intro h
  simp only [List.findM?_cons] at h
  have h1 := (OracleComp.QueriesSatisfy.liftBind_iff.mp h).2 false
  exact (OracleComp.QueriesSatisfy.liftBind_iff.mp h1).1 rfl

/-- The empty search returns `none` and makes no call, whatever the test. -/
example (h : ℕ → ℕ) (test : ℕ → OracleComp (fun _ : ℕ => ℕ) Bool) :
    OracleComp.evalPure h (([] : List ℕ).findM? test) = none ∧
      OracleComp.IsQueryBounded (([] : List ℕ).findM? test) 0 :=
  ⟨by simp, OracleComp.IsCostBounded.findM? (n := 0) (by simp)⟩

/-- The step equations in a monad that is not an oracle program: in `Option`, a failing test
aborts the search. -/
example : [1, 2, 3].findM? (fun x : ℕ => if x = 2 then none else some false) = none := by
  simp [List.findM?_cons]

/-- A failing test after the first accepted element is not run. -/
example : [1, 2, 3].findM? (fun x : ℕ => if x = 2 then none else some true) = some (some 1) := by
  simp [List.findM?_cons]

end CslibFrontierTests.OracleFindM
