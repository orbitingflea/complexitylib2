/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Foundations.Control.Monad.FindM
import Cslib.Foundations.Control.Monad.IsMonadHom.List

/-!
# Monadic list search with an oracle program

Running an oracle test `List.findM?` on a list evaluates against a deterministic oracle as
`List.find?` (`Cslib.OracleComp.evalPure_findM?`), satisfies a cost bound `xs.length * n` when each
test costs at most `n` (`Cslib.OracleComp.IsCostBounded.findM?`), and preserves query predicates
(`Cslib.OracleComp.QueriesSatisfy.findM?`). These are the `List.findM?` counterparts of
`Cslib.OracleComp.IsCostBounded.mapM` and `Cslib.OracleComp.QueriesSatisfy.mapM` in
`CslibFrontier.Languages.Probabilistic.Traverse.SupportWith`.

## Main results

* `Cslib.OracleComp.evalPure_findM?`: deterministic evaluation reduces `findM?` to `List.find?`.
* `Cslib.OracleComp.IsCostBounded.findM?`: a search over `xs` whose tests each cost at most `n`
  costs at most `xs.length * n`.
* `Cslib.OracleComp.QueriesSatisfy.findM?`: a search makes only calls that its tests make.
-/

public section

namespace Cslib.OracleComp

variable {ι : Type} {spec : OracleSpec ι} {α : Type}

/-- Against a deterministic oracle, `findM?` is `find?` on the tests' values: the search returns
the first element whose test evaluates to `true`. -/
@[simp]
theorem evalPure_findM? (h : (q : ι) → spec q) (test : α → OracleComp spec Bool) (xs : List α) :
    evalPure h (xs.findM? test) = xs.find? fun x => evalPure h (test x) := by
  have hom : IsMonadHom (OracleComp spec) Id
      (fun {γ} => interpret (m := Id) (fun q => pure (h q)) (α := γ)) :=
    PFunctor.FreeM.isMonadHom_liftM (P := ⟨ι, spec⟩) (m := Id) fun q => pure (h q)
  unfold evalPure
  rw [hom.map_listFindM?, List.idRun_findM?]
  rfl

/-- A search whose tests each cost at most `n` costs at most `xs.length * n` on every path. The
bound is attained when no test accepts; it does not use that the search stops at the first
accepted element. -/
theorem IsCostBounded.findM? {cost : ι → ℕ} {test : α → OracleComp spec Bool} {n : ℕ}
    {xs : List α} (h : ∀ a ∈ xs, IsCostBounded cost (test a) n) :
    IsCostBounded cost (xs.findM? test) (xs.length * n) := by
  induction xs with
  | nil => rw [List.findM?_nil]; exact .pure _ _
  | cons a xs ih =>
    rw [List.findM?_cons, List.length_cons, Nat.add_mul, one_mul, Nat.add_comm]
    refine (h a List.mem_cons_self).bind fun b => ?_
    cases b with
    | true => exact .pure _ _
    | false => exact ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')

/-- A search whose tests' calls all satisfy `p` makes only calls satisfying `p`. -/
theorem QueriesSatisfy.findM? {p : ι → Prop} {test : α → OracleComp spec Bool} {xs : List α}
    (h : ∀ a ∈ xs, QueriesSatisfy p (test a)) : QueriesSatisfy p (xs.findM? test) := by
  have h' := IsCostBounded.findM? h
  rw [Nat.mul_zero] at h'
  exact h'

end Cslib.OracleComp
