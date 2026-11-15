/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Rat.Floor
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Dyadic approximation modulo one

Rounding each summand down at precision `B` and reducing the sum modulo one gives a
rational point on the circle. The error is at most the number of summands times `2⁻ᴮ`.
The estimate uses integer translates, so it applies to negative and zero targets as well.

This is the rounding step in Section 2, equation `crt-circle-error`, of
[OpenAI2026CountingHierarchy]. No complexity bound or prime-window estimate is claimed.

## Main definitions

* `Cslib.CircleClose`: approximation up to an integer translate.
* `Cslib.dyadicCircleApprox`: sum of rounded fractions, reduced modulo one.

## Main results

* `Cslib.dyadicCircleApprox_close`: the approximation error, including negative targets.

## References

* [OpenAI2026CountingHierarchy], Section 2, proof of Sign from residues.
-/

public section

namespace Cslib

open Finset

/-- Two rational numbers differ by less than `ε`, up to an integer translate. -/
@[expose] def CircleClose (ε u v : ℚ) : Prop := ∃ z : ℤ, |u - v - z| < ε

/-- Sum the numerators obtained by rounding each fraction down at dyadic precision `B`. -/
@[expose] def dyadicSumNumerator {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ) : ℤ :=
  ∑ i, ⌊(2 : ℚ) ^ B * f i⌋

/-- The rounded dyadic sum modulo one. Only the supplied fractions are inputs. -/
@[expose] def dyadicCircleApprox {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ) : ℚ :=
  (dyadicSumNumerator B f % (2 : ℤ) ^ B : ℤ) / (2 : ℚ) ^ B

/-- The dyadic circle approximation is the fractional part of the unwrapped rounded sum. -/
theorem dyadicCircleApprox_eq_fract {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ) :
    dyadicCircleApprox B f = Int.fract ((dyadicSumNumerator B f : ℚ) / (2 : ℚ) ^ B) := by
  simpa only [dyadicCircleApprox, Int.cast_pow, Int.cast_ofNat, Nat.cast_pow, Nat.cast_ofNat] using
    (Int.fract_div_intCast_eq_div_intCast_mod
      (m := dyadicSumNumerator B f) (n := 2 ^ B) (k := ℚ)).symm

/-- The approximation is represented in the half-open unit interval. -/
theorem dyadicCircleApprox_mem {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ) :
    0 ≤ dyadicCircleApprox B f ∧ dyadicCircleApprox B f < 1 := by
  rw [dyadicCircleApprox_eq_fract]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

/-- The unwrapped rounded sum underestimates the sum, by at most one unit per summand. -/
theorem dyadicSumNumerator_error {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ) :
    0 ≤ (∑ i, f i) - (dyadicSumNumerator B f : ℚ) / (2 : ℚ) ^ B ∧
    (∑ i, f i) - (dyadicSumNumerator B f : ℚ) / (2 : ℚ) ^ B ≤
      Fintype.card ι / (2 : ℚ) ^ B := by
  have hD : 0 < (2 : ℚ) ^ B := by positivity
  have heq : (∑ i, f i) - (dyadicSumNumerator B f : ℚ) / (2 : ℚ) ^ B =
      (∑ i, ((2 : ℚ) ^ B * f i - (⌊(2 : ℚ) ^ B * f i⌋ : ℚ))) / (2 : ℚ) ^ B := by
    simp only [dyadicSumNumerator, Int.cast_sum, sum_sub_distrib, ← mul_sum]
    field_simp
  rw [heq]
  constructor
  · exact div_nonneg (sum_nonneg fun i _ => sub_nonneg.mpr (Int.floor_le _)) hD.le
  · apply (div_le_div_iff_of_pos_right hD).mpr
    calc
      _ ≤ ∑ _ : ι, (1 : ℚ) := by
        apply sum_le_sum
        intro i _
        have := Int.sub_one_lt_floor ((2 : ℚ) ^ B * f i)
        linarith
      _ = _ := by simp

/-- Rounding a sum congruent to any rational target gives a circular approximation.
The target may be negative or zero; no choice of its representative is required. -/
theorem dyadicCircleApprox_close {ι : Type*} [Fintype ι] (B : ℕ) (f : ι → ℚ)
    {x ε : ℚ} (h : ∃ z : ℤ, (∑ i, f i) - x = z)
    (hε : Fintype.card ι / (2 : ℚ) ^ B < ε) :
    CircleClose ε (dyadicCircleApprox B f) x := by
  obtain ⟨z, hz⟩ := h
  have herr := dyadicSumNumerator_error B f
  let r : ℚ := (dyadicSumNumerator B f : ℚ) / (2 : ℚ) ^ B
  refine ⟨z - ⌊r⌋, ?_⟩
  rw [dyadicCircleApprox_eq_fract, Int.fract, Int.cast_sub]
  have heq : r - (⌊r⌋ : ℚ) - x - ((z : ℚ) - ⌊r⌋) =
      -((∑ i, f i) - r) := by linarith
  change |r - (⌊r⌋ : ℚ) - x - ((z : ℚ) - ⌊r⌋)| < ε
  rw [heq, abs_neg, abs_of_nonneg herr.1]
  exact herr.2.trans_lt hε

/-- Zero summands have zero approximation, at every precision. -/
@[simp] theorem dyadicCircleApprox_zero {ι : Type*} [Fintype ι] (B : ℕ) :
    dyadicCircleApprox B (fun _ : ι => 0) = 0 := by
  simp [dyadicCircleApprox, dyadicSumNumerator]

end Cslib
