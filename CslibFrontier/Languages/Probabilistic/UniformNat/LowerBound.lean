/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
import Cslib.Probability.PMF
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lower bounds on the residue probabilities of `sampleModNat`

`sampleModNat w m` reduces a number written with `w` fair coins modulo `m`. Each residue `i < m`
is hit by at least `⌊2 ^ w / m⌋` of the `2 ^ w` coin outcomes, so its probability is at least
`(1 - m / 2 ^ w) / m`, that is, `1 / m - 1 / 2 ^ w`. The bound holds for every `w`; it is vacuous
when `2 ^ w ≤ m`.

## Main results

* `Cslib.ProbComp.le_eval_sampleModNat_toReal`: every residue below `m` has probability at least
  `(1 - m / 2 ^ w) / m`, in `ℝ`.
* `Cslib.ProbComp.one_le_mul_eval_sampleModNat_add`: the same bound in `ℝ≥0∞`, without
  subtraction: `1 ≤ m * Pr[i] + m / 2 ^ w`.
-/

public section

namespace Cslib.ProbComp

open Probability
open scoped ENNReal

/-- Pointwise lower bound on `sampleModNat w m`: every residue `i < m` has probability at least
`(1 - m / 2 ^ w) / m`. -/
theorem le_eval_sampleModNat_toReal {w m i : ℕ} (hi : i < m) :
    (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹ ≤
      (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal := by
  have hm : 0 < m := Nat.lt_of_le_of_lt (Nat.zero_le _) hi
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h2w : (0 : ℝ) < (2 : ℝ) ^ w := by positivity
  let Q := 2 ^ w / m
  let emb : Fin Q ↪ Fin (2 ^ w) :=
    ⟨fun q => ⟨q.val * m + i, by
      have hqm : (q.val + 1) * m ≤ Q * m := Nat.mul_le_mul_right m q.isLt
      have hdiv : Q * m ≤ 2 ^ w := Nat.div_mul_le_self (2 ^ w) m
      linarith⟩, by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      exact Fin.ext (Nat.mul_right_cancel hm (by omega))⟩
  have hmod (q : Fin Q) : (emb q).val % m = i := by
    change (q.val * m + i) % m = i
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]
  have hcard : Q ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    calc Q = (Finset.univ.map emb).card := by simp only [Finset.card_map, Finset.card_fin]
      _ ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
        apply Finset.card_le_card
        intro x hx
        obtain ⟨q, -, rfl⟩ := Finset.mem_map.mp hx
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmod q⟩
  have hpmf : (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal =
      ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w := by
    rw [ProbComp.eval_sampleModNat, PMF.map_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    have hfin : ∀ x : Fin (2 ^ w),
        (if i = x.val % m then (((2 : ℝ≥0∞) ^ w)⁻¹ : ℝ≥0∞) else 0) ≠ ⊤ := by
      intro x
      split_ifs
      · exact ENNReal.inv_ne_top.mpr (pow_ne_zero w two_ne_zero)
      · exact ENNReal.zero_ne_top
    rw [ENNReal.toReal_sum (fun x _ => hfin x)]
    calc ∑ x : Fin (2 ^ w), (if i = x.val % m then (((2 : ℝ≥0∞) ^ w)⁻¹ : ℝ≥0∞) else 0).toReal
        = ∑ x : Fin (2 ^ w), if x.val % m = i then ((2 : ℝ) ^ w)⁻¹ else 0 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          by_cases hx : x.val % m = i
          · simp only [hx, ↓reduceIte, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
          · have hx' : i ≠ x.val % m := Ne.symm hx
            simp only [hx, hx', ↓reduceIte, ENNReal.toReal_zero]
      _ = ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) *
            ((2 : ℝ) ^ w)⁻¹ := by
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      _ = ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w :=
          div_eq_mul_inv _ _
  rw [hpmf]
  have hQ_ineq : (2 : ℝ) ^ w - m ≤ (Q : ℝ) * m := by
    have hrem : 2 ^ w < (Q + 1) * m := by
      dsimp only [Q]
      have h1 := Nat.div_add_mod (2 ^ w) m
      have h2 := Nat.mod_lt (2 ^ w) hm
      nlinarith
    have hremR : (2 : ℝ) ^ w ≤ ((Q : ℝ) + 1) * m := by exact_mod_cast hrem.le
    linarith
  have hQ_le : (Q : ℝ) ≤ (Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card := by
    exact_mod_cast hcard
  calc (1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹
      = ((2 : ℝ) ^ w - m) / ((m : ℝ) * (2 : ℝ) ^ w) := by field_simp
    _ ≤ ((Q : ℝ) * m) / ((m : ℝ) * (2 : ℝ) ^ w) := by gcongr
    _ = (Q : ℝ) / (2 : ℝ) ^ w := by field_simp
    _ ≤ ((Finset.univ.filter (fun x : Fin (2 ^ w) => x.val % m = i)).card : ℝ) / (2 : ℝ) ^ w := by
        gcongr

/-- The pointwise lower bound on `sampleModNat w m` in `ℝ≥0∞`, without subtraction: for every
residue `i < m`, `m` times its probability is at least `1 - m / 2 ^ w`. -/
theorem one_le_mul_eval_sampleModNat_add {w m i : ℕ} (hi : i < m) :
    1 ≤ (m : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat w m) i + m / 2 ^ w := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_le i).trans_lt hi
  have hmul : (m : ℝ≥0∞) * ProbComp.eval (ProbComp.sampleModNat w m) i ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (PMF.apply_ne_top _ _)
  have hdiv : (m : ℝ≥0∞) / 2 ^ w ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (pow_ne_zero _ two_ne_zero)
  rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨hmul, hdiv⟩),
    ENNReal.toReal_add hmul hdiv, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  have hcancel :
      (m : ℝ) * ((1 - (m : ℝ) / (2 : ℝ) ^ w) * (m : ℝ)⁻¹) = 1 - (m : ℝ) / (2 : ℝ) ^ w := by
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left (le_eval_sampleModNat_toReal (w := w) hi) hmR.le]

end Cslib.ProbComp
