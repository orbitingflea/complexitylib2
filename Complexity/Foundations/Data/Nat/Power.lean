/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Data/Nat/Basic.lean`)

public import Complexity.Init
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Inequalities on powers of natural numbers

Elementary inequalities on powers and products of natural numbers, in particular powers of two
with scaled exponents: products and sums of quantities bounded by `2 ^ (a * k)` and `2 ^ (b * k)`,
and bounds by exponentials.

## Main results

* `Nat.mul_le_two_pow_add_mul`: `x ≤ 2 ^ (a * k) → y ≤ 2 ^ (b * k) → x * y ≤ 2 ^ ((a + b) * k)`.
* `Nat.add_le_two_pow_add_add_one_mul`:
  `1 ≤ k → x ≤ 2 ^ (a * k) → y ≤ 2 ^ (b * k) → x + y ≤ 2 ^ ((a + b + 1) * k)`.
* `Nat.le_two_pow_mul`: `1 ≤ k → c ≤ 2 ^ (c * k)`.
* `Nat.mul_add_one_pow_le`: `(R + 1) * d ≤ M → R * (M + 1) ^ d ≤ (R + 1) * M ^ d`.
-/

@[expose] public section

namespace Nat

/-- Products of numbers below `2 ^ (a * k)` and `2 ^ (b * k)` are below `2 ^ ((a + b) * k)`. -/
theorem mul_le_two_pow_add_mul {k a b x y : ℕ} (hx : x ≤ 2 ^ (a * k))
    (hy : y ≤ 2 ^ (b * k)) : x * y ≤ 2 ^ ((a + b) * k) := by
  calc
    x * y ≤ 2 ^ (a * k) * 2 ^ (b * k) := Nat.mul_le_mul hx hy
    _ = _ := by rw [← pow_add]; congr 1; ring

/-- Sums of numbers below `2 ^ (a * k)` and `2 ^ (b * k)` are below `2 ^ ((a + b + 1) * k)`. -/
theorem add_le_two_pow_add_add_one_mul {k a b x y : ℕ} (hk : 1 ≤ k) (hx : x ≤ 2 ^ (a * k))
    (hy : y ≤ 2 ^ (b * k)) : x + y ≤ 2 ^ ((a + b + 1) * k) := by
  have hx' : x ≤ 2 ^ ((a + b) * k) := hx.trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))
  have hy' : y ≤ 2 ^ ((a + b) * k) := hy.trans
    (Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by omega)))
  calc
    x + y ≤ 2 ^ ((a + b) * k) * 2 := by omega
    _ = 2 ^ ((a + b) * k + 1) := (pow_succ ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by nlinarith)

/-- A constant `c` is below `2 ^ (c * k)` for `k ≥ 1`. -/
theorem le_two_pow_mul (c k : ℕ) (hk : 1 ≤ k) : c ≤ 2 ^ (c * k) :=
  Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by omega) (by nlinarith))

/-- `(1 + 1 / M) ^ d ≤ 1 + 1 / R` when `(R + 1) d ≤ M`, without denominators. -/
theorem mul_add_one_pow_le {R M d : ℕ} (h : (R + 1) * d ≤ M) :
    R * (M + 1) ^ d ≤ (R + 1) * M ^ d := by
  -- `(M + 1) ^ d * (M - d) ≤ M ^ (d + 1)` by induction.
  have key : ∀ e : ℕ, e ≤ M → (M + 1) ^ e * (M - e) ≤ M ^ (e + 1) := by
    intro e
    induction e with
    | zero => intro _; simp
    | succ e ih =>
      intro he
      have ih := ih (by omega)
      have hstep : (M + 1) * (M - (e + 1)) ≤ M * (M - e) := by
        obtain ⟨r, rfl⟩ : ∃ r, M = e + 1 + r := ⟨M - (e + 1), by omega⟩
        rw [show e + 1 + r - (e + 1) = r by omega, show e + 1 + r - e = r + 1 by omega]
        nlinarith
      calc (M + 1) ^ (e + 1) * (M - (e + 1)) = (M + 1) ^ e * ((M + 1) * (M - (e + 1))) := by
            ring
        _ ≤ (M + 1) ^ e * (M * (M - e)) := Nat.mul_le_mul_left _ hstep
        _ = M * ((M + 1) ^ e * (M - e)) := by ring
        _ ≤ M * M ^ (e + 1) := Nat.mul_le_mul_left _ ih
        _ = M ^ (e + 1 + 1) := by ring
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  have hdM : d < M := by nlinarith
  have hpos : 0 < M - d := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hpos
  calc R * (M + 1) ^ d * (M - d) = R * ((M + 1) ^ d * (M - d)) := by ring
    _ ≤ R * M ^ (d + 1) := Nat.mul_le_mul_left _ (key d hdM.le)
    _ = M ^ d * (R * M) := by ring
    _ ≤ M ^ d * ((R + 1) * (M - d)) := by
        refine Nat.mul_le_mul_left _ ?_
        obtain ⟨r, rfl⟩ : ∃ r, M = d + r := ⟨M - d, by omega⟩
        rw [show d + r - d = r by omega]
        nlinarith
    _ = (R + 1) * M ^ d * (M - d) := by ring

end Nat
