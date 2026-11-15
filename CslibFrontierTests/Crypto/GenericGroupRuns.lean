/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

-- `import all`: the runs below evaluate the unexposed bodies of `answer` and `babyStepGiantStep`,
-- and of the private helpers `walk` and `firstMatch` of the latter.
import all CslibFrontier.Crypto.Computational.GenericGroup.Basic
import all CslibFrontier.Crypto.Computational.GenericGroup.BabyStepGiantStep

/-!
# The generic group oracle and baby-step/giant-step: concrete runs

Runs `babyStepGiantStep` against the oracle of `ZMod q` by `decide`, and shows that the
hypotheses of the correctness theorems are needed:

* in `ZMod 11` with base point `1`, the book's table size `4 = ⌈11^(1/2)⌉` and brute force
  (`m = 11`, `n = 1`) output the discrete logarithm;
* `q ≤ m * n` is needed: in `ZMod 11` with `m = n = 3`, the logarithm `4` is missed and the
  program outputs `0`;
* injectivity of `β ↦ β • g` is needed: in `ZMod 4` with `g = 2` and `m = n = 2`, the logarithm
  `3` is missed;
* surjectivity of `β ↦ β • g` is needed in `groupAnswer_eq_answer`: in `ZMod 4` with `g = 2`, the
  group operation on `1`, which is not a multiple of `2`, gets `some 2` from the group and `none`
  from the generic group oracle.
-/

-- This regression module exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GenericGroupRuns

open Cslib Cslib.Crypto.GenericGroup

/-! ### Runs in `ZMod 11` -/

example : (babyStepGiantStep 4 4 (1 : ZMod 11) 7).evalPure (groupAnswer 11 1) = 7 := by decide

example : (babyStepGiantStep 4 4 (1 : ZMod 11) 0).evalPure (groupAnswer 11 1) = 0 := by decide

example : (babyStepGiantStep 11 1 (1 : ZMod 11) 9).evalPure (groupAnswer 11 1) = 9 := by decide

/-! ### The hypotheses are needed -/

/-- `q ≤ m * n` is needed: with `m = n = 3` in `ZMod 11`, the outputs `β - 3 * γ` for
`β ∈ {1, 2, 3}` and `γ ∈ {0, 1, 2}` miss `4` and `5`. -/
example : (babyStepGiantStep 3 3 (1 : ZMod 11) 4).evalPure (groupAnswer 11 1) ≠ 4 := by decide

/-- Injectivity of `β ↦ β • g` is needed: `2` has order `2` in `ZMod 4`, and the program outputs
`1` on the input `3 • 2`. -/
example : (babyStepGiantStep 2 2 (2 : ZMod 4) (3 • 2)).evalPure (groupAnswer 4 2) ≠ 3 := by
  decide

/-- Surjectivity of `β ↦ β • g` is needed in `groupAnswer_eq_answer`: the group answers a group
operation on `1`, which is not a multiple of `2` in `ZMod 4`. -/
example : groupAnswer 4 (2 : ZMod 4) (.op 1 1 1 1) = some 2 := by decide

/-- The generic group oracle of `β ↦ β • 2` rejects the same query. -/
example : answer (fun β : ZMod 4 => β • (2 : ZMod 4)) (.op 1 1 1 1) = none := by
  have h : Function.partialInv (fun β : ZMod 4 => β • (2 : ZMod 4)) 1 = none :=
    dite_eq_right (by decide)
  change (Function.partialInv _ 1).bind _ = none
  rw [h]
  rfl

end CslibFrontierTests.Crypto.GenericGroupRuns
