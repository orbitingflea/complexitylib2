/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.NumberTheory.DyadicCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Recovering a sign by the first flagged doubling

Successive doublings of a small nonzero rational eventually enter a prescribed magnitude
window. A sufficiently accurate approximation modulo one is then flagged, and its first
flag lies on the correct side of one half. The threshold, flag margin, error and final index
are parameters. In particular, a caller supplies the magnitude/product and precision bounds,
not a correctness assertion about the sign procedure.

This is the mathematical first-flag argument of Section 2 of
[OpenAI2026CountingHierarchy], generalized beyond its fixed constants. There is no
complexity membership claim.

## Main definitions

* `Cslib.CircleFlag`: the symmetric interval used to flag an approximation.
* `Cslib.FirstCircleFlag`: the first flagged index of a sequence.

## Main results

* `Cslib.firstCircleFlag_sign`: the side of one half at the first flag determines the sign.

## References

* [OpenAI2026CountingHierarchy], Section 2, proof of Sign from residues.
-/

public section

namespace Cslib

/-- An approximation is flagged when it stays at least `t` away from either endpoint. -/
@[expose] def CircleFlag (t w : ℚ) : Prop := t ≤ w ∧ w ≤ 1 - t

/-- Index `k` is flagged and every preceding index is unflagged. -/
@[expose] def FirstCircleFlag (t : ℚ) (w : ℕ → ℚ) (k : ℕ) : Prop :=
  CircleFlag t (w k) ∧ ∀ j < k, ¬ CircleFlag t (w j)

/-- No approximation of zero can be flagged when the error is below the flag margin. -/
theorem CircleClose.not_flag_zero {ε t w : ℚ} (h : CircleClose ε w 0)
    (hε : ε < t) : ¬ CircleFlag t w := by
  obtain ⟨z, hz⟩ := h
  intro hf
  have hz' := abs_lt.mp hz
  have hzl : (0 : ℚ) < z := by linarith [hf.1]
  have hzu : (z : ℚ) < 1 := by linarith [hf.2]
  have hzl' : 0 < z := by exact_mod_cast hzl
  have hzu' : z < 1 := by exact_mod_cast hzu
  omega


/-- A flag excludes wrapping at zero; a small target has the sign indicated by the
side of one half. This also rules out a flag for a zero target. -/
theorem CircleClose.sign_of_flag {ε t b w q : ℚ} (h : CircleClose ε w q)
    (hf : CircleFlag t w) (hε : ε < t) (hb : b + ε ≤ 1 / 2) (hq : |q| < b) :
    (0 < q ↔ w < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w) := by
  have hnzero : q ≠ 0 := by
    intro hzero
    subst q
    exact h.not_flag_zero hε hf
  obtain ⟨z, hz⟩ := h
  have hz' := abs_lt.mp hz
  have hq' := abs_lt.mp hq
  obtain hpos | hzero | hneg := lt_trichotomy 0 q
  · have hzlo : (-1 : ℚ) < z := by linarith [hf.1]
    have hzhi : (z : ℚ) < 1 := by linarith [hf.2]
    have hzlo' : -1 < z := by exact_mod_cast hzlo
    have hzhi' : z < 1 := by exact_mod_cast hzhi
    have hzz : z = 0 := by omega
    subst z
    norm_num at hz'
    have hw : w < 1 / 2 := by linarith
    exact ⟨iff_of_true hpos hw, iff_of_false (by linarith) (by linarith)⟩
  · exact False.elim (hnzero hzero.symm)
  · have hzlo : (0 : ℚ) < z := by linarith [hf.1]
    have hzhi : (z : ℚ) < 2 := by linarith [hf.2]
    have hzlo' : 0 < z := by exact_mod_cast hzlo
    have hzhi' : z < 2 := by exact_mod_cast hzhi
    have hzz : z = 1 := by omega
    subst z
    norm_num at hz'
    have hw : 1 / 2 < w := by linarith
    exact ⟨iff_of_false (by linarith) (by linarith), iff_of_true hneg hw⟩

/-- A target whose magnitude is between `a` and `b` must be flagged, provided the
rounding error fits between that window and the endpoints. -/
theorem CircleClose.flag_of_magnitude {ε t a b w q : ℚ} (h : CircleClose ε w q)
    (hw : 0 ≤ w ∧ w < 1) (hlo : t + ε ≤ a) (hhi : b + ε ≤ 1 - t)
    (ht : 0 < t) (hqlo : a ≤ |q|) (hqhi : |q| < b) : CircleFlag t w := by
  obtain ⟨z, hz⟩ := h
  have hz' := abs_lt.mp hz
  have hq' := abs_lt.mp hqhi
  have hεpos : 0 < ε := lt_of_le_of_lt (abs_nonneg _) hz
  obtain hpos | hneg := le_total 0 q
  · rw [abs_of_nonneg hpos] at hqlo
    have hzlo : (-1 : ℚ) < z := by linarith [hw.1]
    have hzhi : (z : ℚ) < 1 := by linarith [hw.2]
    have hzlo' : -1 < z := by exact_mod_cast hzlo
    have hzhi' : z < 1 := by exact_mod_cast hzhi
    have hzz : z = 0 := by omega
    subst z
    constructor <;> norm_num at hz' <;> linarith
  · rw [abs_of_nonpos hneg] at hqlo
    have hzlo : (0 : ℚ) < z := by linarith [hw.1]
    have hzhi : (z : ℚ) < 2 := by linarith [hw.2]
    have hzlo' : 0 < z := by exact_mod_cast hzlo
    have hzhi' : z < 2 := by exact_mod_cast hzhi
    have hzz : z = 1 := by omega
    subst z
    constructor <;> norm_num at hz' <;> linarith

/-- At the first doubling reaching magnitude `a`, the magnitude is still below `2a`.
The final-index condition is a numerical bound, not a first-flag correctness premise. -/
theorem exists_first_doubling_magnitude {q a : ℚ} {K : ℕ}
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|) :
    ∃ k ≤ K, a ≤ |(2 : ℚ) ^ k * q| ∧
      ∀ j ≤ k, |(2 : ℚ) ^ j * q| < 2 * a := by
  let P : ℕ → Prop := fun k => a ≤ |(2 : ℚ) ^ k * q|
  have hex : ∃ k, P k := ⟨K, hend⟩
  let k := Nat.find hex
  have hk : k ≤ K := Nat.find_min' hex hend
  have hkpos : 0 < k := by
    by_contra hn
    have hzero : k = 0 := by omega
    have hspec : a ≤ |(2 : ℚ) ^ k * q| := Nat.find_spec hex
    rw [hzero] at hspec
    norm_num at hspec
    linarith
  have hprev : |(2 : ℚ) ^ (k - 1) * q| < a := by
    exact lt_of_not_ge (Nat.find_min hex (by omega))
  have hkbound : |(2 : ℚ) ^ k * q| < 2 * a := by
    have heq : k = (k - 1) + 1 := by omega
    calc
      |(2 : ℚ) ^ k * q| = 2 * |(2 : ℚ) ^ (k - 1) * q| := by
        rw [heq, pow_succ, show (2 : ℚ) ^ (k - 1) * 2 * q =
          2 * ((2 : ℚ) ^ (k - 1) * q) by ring, abs_mul]
        norm_num
      _ < 2 * a := mul_lt_mul_of_pos_left hprev (by norm_num)
  refine ⟨k, hk, Nat.find_spec hex, fun j hj => ?_⟩
  have hpow : (2 : ℚ) ^ j ≤ (2 : ℚ) ^ k := pow_le_pow_right₀ (by norm_num) hj
  calc
    |(2 : ℚ) ^ j * q| = (2 : ℚ) ^ j * |q| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)]
    _ ≤ (2 : ℚ) ^ k * |q| := mul_le_mul_of_nonneg_right hpow (abs_nonneg q)
    _ = |(2 : ℚ) ^ k * q| := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℚ) ≤ 2) _)]
    _ < 2 * a := hkbound

/-- Mathematical correctness of first-flag sign recovery. Approximation, magnitude,
precision, flag margin and cutoff conditions are independent explicit inputs. -/
theorem firstCircleFlag_sign {q a ε t : ℚ} {K : ℕ} (w : ℕ → ℚ)
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|)
    (ht : 0 < t) (hε : ε < t) (hlo : t + ε ≤ a) (hhi : 2 * a + ε ≤ 1 / 2)
    (hw : ∀ k ≤ K, 0 ≤ w k ∧ w k < 1)
    (happrox : ∀ k ≤ K, CircleClose ε (w k) ((2 : ℚ) ^ k * q)) :
    ∃ k ≤ K, FirstCircleFlag t w k ∧
      (0 < q ↔ w k < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w k) := by
  classical
  obtain ⟨k₀, hk₀, hreach, hbound⟩ := exists_first_doubling_magnitude hstart hend
  have hεpos : 0 < ε := by
    obtain ⟨z, hz⟩ := happrox k₀ hk₀
    exact (abs_nonneg _).trans_lt hz
  have ht_half : t < 1 / 2 := by linarith
  have hflag : CircleFlag t (w k₀) :=
    (happrox k₀ hk₀).flag_of_magnitude (hw k₀ hk₀) hlo (by linarith) ht
      hreach (hbound k₀ le_rfl)
  have hex : ∃ k, CircleFlag t (w k) := ⟨k₀, hflag⟩
  let k := Nat.find hex
  have hk₀' : k ≤ k₀ := Nat.find_min' hex hflag
  have hk : k ≤ K := hk₀'.trans hk₀
  have hs := (happrox k hk).sign_of_flag (Nat.find_spec hex) hε hhi (hbound k hk₀')
  refine ⟨k, hk, ⟨Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩, ?_, ?_⟩
  · simpa only [mul_pos_iff_of_pos_left (by positivity : 0 < (2 : ℚ) ^ k)] using hs.1
  · have hp : 0 < (2 : ℚ) ^ k := by positivity
    have heq : (2 : ℚ) ^ k * q < 0 ↔ q < 0 := by
      simpa only [mul_zero] using (mul_lt_mul_iff_right₀ hp :
        (2 : ℚ) ^ k * q < (2 : ℚ) ^ k * 0 ↔ q < 0)
    exact heq.symm.trans hs.2

/-- The first flagged index is unique, without any approximation hypotheses. -/
theorem FirstCircleFlag.unique {t : ℚ} {w : ℕ → ℚ} {j k : ℕ}
    (hj : FirstCircleFlag t w j) (hk : FirstCircleFlag t w k) : j = k := by
  obtain hlt | heq | hgt := lt_trichotomy j k
  · exact False.elim (hk.2 j hlt hj.1)
  · exact heq
  · exact False.elim (hj.2 k hgt hk.1)

/-- Any first flagged index has the correct sign, under the numerical doubling bounds. -/
theorem FirstCircleFlag.sign {q a ε t : ℚ} {K k : ℕ} {w : ℕ → ℚ}
    (hf : FirstCircleFlag t w k)
    (hstart : |q| < a) (hend : a ≤ |(2 : ℚ) ^ K * q|)
    (ht : 0 < t) (hε : ε < t) (hlo : t + ε ≤ a) (hhi : 2 * a + ε ≤ 1 / 2)
    (hw : ∀ j ≤ K, 0 ≤ w j ∧ w j < 1)
    (happrox : ∀ j ≤ K, CircleClose ε (w j) ((2 : ℚ) ^ j * q)) :
    k ≤ K ∧ (0 < q ↔ w k < 1 / 2) ∧ (q < 0 ↔ 1 / 2 < w k) := by
  obtain ⟨j, hj, hf', hs⟩ := firstCircleFlag_sign w hstart hend ht hε hlo hhi hw happrox
  obtain rfl := hf.unique hf'
  exact ⟨hj, hs⟩


end Cslib
