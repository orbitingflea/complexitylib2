/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Crypto.Computational.Pseudoentropy.Boosting.Training
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.PPT

/-! Ordinary-module clients of the complete plain boosting certificate family. -/

public section

namespace CslibFrontierTests.PseudoentropyBoostingPlain

open Cslib Cslib.Probability Cslib.Crypto.Pseudoentropy.Boosting Cslib.BitString
  Turing.MultiTapeTM

-- The joint evaluator sees the stored code and the observation captured from the original input.
example : ComputableInPolyTime (fun word : List Bool =>
    (State.mk false word.length [word]).votes
      (fun code observation => code.isEmpty == observation.isEmpty) word) encBits encBits := by
  apply State.isPolyTime_votes
  · fun_prop
  · apply State.isPolyTime_mk <;> fun_prop
  · fun_prop

-- Raw vote order is preserved, including empty stored descriptions and an empty observation.
example : (State.mk false 0 [[], [true], []]).votes
    (fun code observation => code.isEmpty == observation.isEmpty) [] = [true, false, true] := by
  decide

-- Captured observations and a computed truncation bound pass through the full sampled loop.
example : IsPPTOn encBits State.encoding (fun word =>
    run (fun code observation => listStrictMajority (code ++ observation))
      (pure (word, true)) (fun state => pure (word.take (state.threshold + 1)))
      { confidence := word.length + 1, densityNumerator := 0, densityBound := 0,
        rateBound := 0, codeBound := word.length }) := by
  ppt

-- The final selector and predictor compose with the same captured-input learner and parameters.
example : IsPPTOn encBits encBool (fun word => do
    let params : Parameters := ⟨word.length + 1, 0, 0, 0, word.length⟩
    let model ← train (fun code observation => listStrictMajority (code ++ observation))
      (pure (word, true)) (fun state => pure (word.take (state.threshold + 1))) params
    predict (fun code observation => listStrictMajority (code ++ observation))
      params.predictionGridBound model word) := by
  ppt

-- A stopped empty model ignores sampling precision and returns its deterministic majority.
example : predict (fun _ _ => false) 0 (⟨true, 0, []⟩, 0) [] = pure false := rfl

end CslibFrontierTests.PseudoentropyBoostingPlain
