/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Foundations.Algebra.Group.ZPowCoprime
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Tactic.NormNum

/-!
# Common roots for coprime integer exponents: checked instances

Checks for `CslibFrontier/Foundations/Algebra/Group/ZPowCoprime.lean`:

* The root `y ^ s * w ^ t` with Mathlib's Bézout coefficients `Int.gcdA`, `Int.gcdB`, the warm-up
  `e = 3`, `f = 2` with root `y / w`, a negative exponent in the hypothesis, and the edge case
  `m = 1`, `n = 0`.
* A concrete instance in `(ZMod 35)ˣ` with a negative Bézout coefficient, evaluated.
* Two client steps: a prime `e` and `0 < |f| < e` give `IsCoprime e f`, and the characterization
  splits one relation `πx ^ p = πy ^ r` into a common root. The characterization also applies to
  commuting elements of `Equiv.Perm (Fin 3)`.
* The hypotheses are needed: coprimality in `(ZMod 3)ˣ` and for `m = n = 0`, commutativity in
  `Equiv.Perm (Fin 3)`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Foundations.Algebra.ZPowCoprime

/-! ### The root formula -/

/-- The root `y ^ s * w ^ t` of `y`, with Mathlib's extended Euclidean coefficients
`s = Int.gcdA e f`, `t = Int.gcdB e f`. -/
example {N : ℕ} (e f : ℤ) (w y : (ZMod N)ˣ) (hef : Int.gcd e f = 1) (h : w ^ e = y ^ f) :
    (y ^ Int.gcdA e f * w ^ Int.gcdB e f) ^ e = y :=
  (Commute.all w y).zpow_mul_zpow_zpow_eq_right
    (by have := Int.gcd_eq_gcd_ab e f; rw [hef] at this; exact_mod_cast this.symm) h

/-- The same element is an `f`-th root of `w`. -/
example {N : ℕ} (e f : ℤ) (w y : (ZMod N)ˣ) (hef : Int.gcd e f = 1) (h : w ^ e = y ^ f) :
    (y ^ Int.gcdA e f * w ^ Int.gcdB e f) ^ f = w :=
  (Commute.all w y).zpow_mul_zpow_zpow_eq_left
    (by have := Int.gcd_eq_gcd_ab e f; rw [hef] at this; exact_mod_cast this.symm) h

/-- The warm-up `e = 3`, `f = 2`: from `w ^ 3 = y ^ 2`, `(y / w) ^ 3 = y` (`s = 1`, `t = -1`). -/
example {N : ℕ} (w y : (ZMod N)ˣ) (h : w ^ (3 : ℤ) = y ^ (2 : ℤ)) : (y / w) ^ 3 = y := by
  have := (Commute.all w y).zpow_mul_zpow_zpow_eq_right (s := 1) (t := -1) (by norm_num) h
  rw [zpow_one, zpow_neg_one, ← div_eq_mul_inv] at this
  exact_mod_cast this

/-- A negative exponent in the hypothesis: `w ^ 5 = y ^ (-3)` gives `(y ^ 2 * w ^ 3) ^ 5 = y`. -/
example {N : ℕ} (w y : (ZMod N)ˣ) (h : w ^ (5 : ℤ) = y ^ (-3 : ℤ)) :
    (y ^ (2 : ℤ) * w ^ (3 : ℤ)) ^ (5 : ℤ) = y :=
  (Commute.all w y).zpow_mul_zpow_zpow_eq_right (by norm_num) h

/-- Edge case `m = 1`, `n = 0`, which are coprime: then `a = b ^ 0 = 1` and the root is `b`. -/
example {N : ℕ} (a b : (ZMod N)ˣ) (h : a ^ (1 : ℤ) = b ^ (0 : ℤ)) :
    (b ^ (1 : ℤ) * a ^ (0 : ℤ)) ^ (1 : ℤ) = b :=
  (Commute.all a b).zpow_mul_zpow_zpow_eq_right (by norm_num) h

/-- Uniqueness needs no commutativity: in any group, an element with `c ^ 2 = b` and `c ^ 3 = a`
is `b ^ (-1) * a`. -/
example {G : Type*} [Group G] {a b c : G} (hb : c ^ (2 : ℤ) = b) (ha : c ^ (3 : ℤ) = a) :
    c = b ^ (-1 : ℤ) * a ^ (1 : ℤ) :=
  eq_zpow_mul_zpow_of_zpow_eq (by norm_num) hb ha

/-- The additive form, in `ℤ`: `3 • 10 = 2 • 15` gives the common root `5 = 1 • 15 + (-1) • 10`. -/
example : (1 : ℤ) • (15 : ℤ) + (-1 : ℤ) • (10 : ℤ) = 5 ∧
    (3 : ℤ) • ((1 : ℤ) • (15 : ℤ) + (-1 : ℤ) • (10 : ℤ)) = 15 :=
  ⟨by norm_num, AddCommute.zsmul_add_zsmul_zsmul_eq_right (n := 2) (AddCommute.all _ _)
    (by norm_num) (by norm_num)⟩

/-! ### A concrete instance in `(ZMod 35)ˣ` -/

/-- `32 = 2 ^ 5` as a unit modulo `35`, with inverse `23`. The inverse is explicit so that `decide`
evaluates negative powers; `ZMod.unitOfCoprime` does not reduce under `decide`. -/
def a35 : (ZMod 35)ˣ := ⟨32, 23, by decide, by decide⟩

/-- `8 = 2 ^ 3` as a unit modulo `35`, with inverse `22`. -/
def b35 : (ZMod 35)ˣ := ⟨8, 22, by decide, by decide⟩

example : a35 ^ (3 : ℤ) = b35 ^ (5 : ℤ) := by decide

/-- With `3 * 2 + 5 * (-1) = 1`, the root `b ^ 2 * a ^ (-1)` is `2`. -/
example : ((b35 ^ (2 : ℤ) * a35 ^ (-1 : ℤ) : (ZMod 35)ˣ) : ZMod 35) = 2 := by decide

example : (b35 ^ (2 : ℤ) * a35 ^ (-1 : ℤ)) ^ (3 : ℤ) = b35 :=
  (Commute.all a35 b35).zpow_mul_zpow_zpow_eq_right (n := 5) (by norm_num) (by decide)

example : (b35 ^ (2 : ℤ) * a35 ^ (-1 : ℤ)) ^ (5 : ℤ) = a35 :=
  (Commute.all a35 b35).zpow_mul_zpow_zpow_eq_left (m := 3) (by norm_num) (by decide)

/-! ### Client steps -/

/-- The step before the identity in the proof of Theorem 10.7 of [BonehShoup2023]: a prime `e`
and `f ≠ 0` with `|f| < e` are coprime. -/
example {e : ℕ} (he : e.Prime) {f : ℤ} (hf : f ≠ 0) (hlt : |f| < e) : IsCoprime (e : ℤ) f :=
  ((Nat.prime_iff_prime_int.mp he).irreducible.coprime_iff_not_dvd).mpr
    fun hdvd => hf (Int.eq_zero_of_abs_lt_dvd hdvd hlt)

/-- Splitting an aggregated relation: from `πx ^ p = πy ^ r` with `p`, `r` coprime, one element
`π` has `π ^ r = πx` and `π ^ p = πy`. -/
example {N : ℕ} (πx πy : (ZMod N)ˣ) {p r : ℤ} (hpr : IsCoprime p r) (h : πx ^ p = πy ^ r) :
    ∃ π : (ZMod N)ˣ, π ^ r = πx ∧ π ^ p = πy := by
  obtain ⟨π, h1, h2⟩ := (zpow_eq_zpow_iff_of_isCoprime hpr).mp h
  exact ⟨π, h1.symm, h2.symm⟩

/-- The characterization for commuting elements of a noncommutative group: `c ^ 3` and `c ^ 2`
commute in `Equiv.Perm (Fin 3)`, and `2`, `3` are coprime. -/
example (c : Equiv.Perm (Fin 3)) :
    (c ^ (3 : ℤ)) ^ (2 : ℤ) = (c ^ (2 : ℤ)) ^ (3 : ℤ) ↔
      ∃ d, c ^ (3 : ℤ) = d ^ (3 : ℤ) ∧ c ^ (2 : ℤ) = d ^ (2 : ℤ) :=
  ((Commute.refl c).zpow_zpow 3 2).zpow_eq_zpow_iff_of_isCoprime ⟨-1, 1, by norm_num⟩

/-! ### The hypotheses are needed -/

/-- Coprimality: in `(ZMod 3)ˣ`, `1 ^ 2 = (-1) ^ 2`, and `-1` is not a square. -/
example : ∃ w y : (ZMod 3)ˣ, w ^ (2 : ℤ) = y ^ (2 : ℤ) ∧ ∀ c : (ZMod 3)ˣ, c ^ (2 : ℤ) ≠ y :=
  ⟨1, -1, by decide, by decide⟩

/-- Coprimality, with `m = n = 0`: `a ^ 0 = b ^ 0` always holds, a common root would force
`a = 1`, and `0`, `0` are not coprime. -/
example : ¬ IsCoprime (0 : ℤ) 0 ∧ ∃ a b : (ZMod 3)ˣ, a ^ (0 : ℤ) = b ^ (0 : ℤ) ∧
    ¬ ∃ c : (ZMod 3)ˣ, a = c ^ (0 : ℤ) ∧ b = c ^ (0 : ℤ) :=
  ⟨by rw [isCoprime_zero_left]; exact not_isUnit_zero, -1, 1, by decide, by decide⟩

/-- Commutativity: a transposition `a` and a 3-cycle `b` in `Equiv.Perm (Fin 3)` have
`a ^ 2 = b ^ 3` with `2 * (-1) + 3 * 1 = 1`, but `(b ^ (-1) * a) ^ 2 ≠ b`, and no `c` has
`a = c ^ 3` and `b = c ^ 2`. -/
example : ∃ a b : Equiv.Perm (Fin 3), a ^ (2 : ℤ) = b ^ (3 : ℤ) ∧
    (b ^ (-1 : ℤ) * a ^ (1 : ℤ)) ^ (2 : ℤ) ≠ b ∧
    ¬ ∃ c : Equiv.Perm (Fin 3), a = c ^ (3 : ℤ) ∧ b = c ^ (2 : ℤ) :=
  ⟨Equiv.swap 0 1, Equiv.swap 0 1 * Equiv.swap 1 2, by decide, by decide, by decide⟩

end CslibFrontierTests.Foundations.Algebra.ZPowCoprime
