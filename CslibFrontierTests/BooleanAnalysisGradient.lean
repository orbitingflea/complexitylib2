/-
Copyright (c) 2026 Vincent Liew. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Liew
-/

module

import CslibFrontier.Foundations.BooleanAnalysis.Influence
import Mathlib.Tactic.FinCases

/-! # The gradient of the conjunction of two bits

Read as signs, the conjunction of two bits has gradient `(1, 1)` at `(true, true)`, where both
bits are sensitive, so its squared norm there is the sensitivity `2`. Over the four inputs the
squared norms are the sensitivities `2, 1, 1, 0`, and their mean `1` is the total influence of
the conjunction by Proposition 2.35.
-/

namespace CslibFrontierTests.BooleanAnalysisGradient

open Cslib Cslib.BitString Finset

-- The gradient of the conjunction at `(true, true)` is `(1, 1)`: both bits are sensitive there.
example : gradient (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) (fun _ => true) =
    fun _ => 1 := by
  funext i
  fin_cases i <;> simp [gradient, derivative, Function.update]

-- Its squared norm there is the sensitivity `2`.
example : ∑ i, gradient (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) (fun _ => true) i ^ 2 =
    2 := by
  rw [sum_gradient_signVal_sq (fun x : Fin 2 → Bool => x 0 && x 1),
    show (2 : ℝ) = (2 : ℕ) by norm_num, Nat.cast_inj]
  decide

-- The squared norms, the sensitivities `2, 1, 1, 0`, average to the total influence `1`.
example : totalInfluence (fun x : Fin 2 → Bool => signVal (x 0 && x 1)) = 1 := by
  rw [totalInfluence_eq_expect_sum_gradient_sq]
  simp only [sum_gradient_signVal_sq (fun x : Fin 2 → Bool => x 0 && x 1),
    expect_eq_sum_div_card, ← Nat.cast_sum]
  rw [(by decide : ∑ x : Fin 2 → Bool,
    #{i | (Function.update x i (!x i) 0 && Function.update x i (!x i) 1) ≠ (x 0 && x 1)} = 4)]
  norm_num [Fintype.card_fun]

end CslibFrontierTests.BooleanAnalysisGradient
