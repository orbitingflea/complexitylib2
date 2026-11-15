/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Foundations.NumberTheory.PrimeWindowBounds

/-!
# Prime-window bounds through ordinary imports

Concrete endpoint checks supplement the symbolic cutoff client: the lower endpoint is excluded,
the upper endpoint is included, and an empty window has product one.
-/

set_option linter.privateModule false

open Finset

example : Nat.primesLE 11 \ Nat.primesLE 5 = {7, 11} := by decide

example : (∏ p ∈ Nat.primesLE 11 \ Nat.primesLE 5, p) = 77 := by decide

example : (∏ p ∈ Nat.primesLE 5 \ Nat.primesLE 11, p) = 1 := by decide

example {p : ℕ} (hp : p ∈ Nat.primesLE 11 \ Nat.primesLE 5) : 5 < p ∧ p ≤ 11 := by
  obtain ⟨_, hlo, hhi⟩ := Nat.mem_primesLE_sdiff_primesLE_iff.mp hp
  exact ⟨hlo, hhi⟩

-- The manuscript's complete numerical contract, with its actual three input bounds.
example (m L : ℕ) :
    let Z := max 16 (max m L)
    let Y := 2 * Z ^ 4
    3 * Z ≤ #(Nat.primesLE Y \ Nat.primesLE L) ∧
      2 ^ (3 * Z) ≤ (∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p) ∧
      (∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p) ≤ 2 ^ (Y * Y.size) ∧
      6 * 2 ^ m < (∏ p ∈ Nat.primesLE Y \ Nat.primesLE L, p) := by
  dsimp only
  have hZ : 16 ≤ max 16 (max m L) := le_max_left _ _
  have hm : m ≤ max 16 (max m L) := (le_max_left m L).trans (le_max_right _ _)
  have hL : L ≤ max 16 (max m L) := (le_max_right m L).trans (le_max_right _ _)
  exact ⟨Nat.three_mul_le_card_primesLE_sdiff hZ hL,
    Nat.two_pow_three_mul_le_prod_primesLE_sdiff hZ hL,
    Nat.prod_primesLE_sdiff_le_two_pow _ _,
    Nat.six_mul_two_pow_lt_prod_primesLE_sdiff hZ hL hm⟩

example {Z k : ℕ} (hk : k ≤ (2 * Z ^ 4) * (2 * Z ^ 4).size + 1) :
    k.size + ((2 * Z ^ 4).size + 10).size ≤ 12 * Z.size + 16 := by
  have := Nat.size_prime_window_doubling_index_le hk
  have := Nat.size_prime_window_precision_le Z
  omega

example : (2 * 16 ^ 4).size = 18 := by decide
