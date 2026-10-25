/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.PCP.TwoProverGame

/-! # Two-prover one-round games

The CHSH game: the constant strategies win with probability `3/4`, so its value is at least `3/4`
and the value of its `n`-fold repetition is at least `(3/4)^n`. A game that accepts every answer
has value one.
-/

namespace ComplexityTests.TwoProverGame

open Cslib.PCP

/-- The **CHSH game**: uniform questions `x, y`, accepted when `a xor b = x && y`. -/
noncomputable def chsh : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts x y a b := (a ^^ b) = (x && y)

theorem winProb_chsh_const : chsh.winProb (fun _ => false) (fun _ => false) = 3 / 4 := by
  rw [TwoProverGame.winProb, Cslib.Probability.PMF.toOuterMeasure_apply_toReal]
  simp [chsh, Cslib.Probability.PMF.uniformOfFintype_apply, Fintype.sum_prod_type]
  norm_num

example : 3 / 4 ≤ chsh.value := winProb_chsh_const ▸ chsh.winProb_le_value _ _

example (n : ℕ) : (3 / 4 : ℝ) ^ n ≤ (chsh.pow n).value := by
  rw [← winProb_chsh_const, ← chsh.winProb_pow n]
  exact (chsh.pow n).winProb_le_value _ _

/-- A game that accepts every answer. -/
noncomputable def always : TwoProverGame Bool Bool Bool Bool where
  questions := Cslib.Probability.PMF.uniformOfFintype (Bool × Bool)
  accepts _ _ _ _ := True

example : always.value = 1 := by
  refine le_antisymm always.value_le_one ?_
  have : always.winProb (fun _ => true) (fun _ => true) = 1 := by
    simp [TwoProverGame.winProb, always]
  exact this ▸ always.winProb_le_value _ _

end ComplexityTests.TwoProverGame
