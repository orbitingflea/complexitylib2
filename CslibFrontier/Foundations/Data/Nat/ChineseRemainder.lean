/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.ZMod.NatCast
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Two-modulus Chinese Remainder recombination

`crtCombine D L a xL inv = a + D * ((xL - a) * inv mod L)` recombines a residue `a` modulo `D`
and a residue `xL` modulo `L`, given an inverse `inv` of `D` modulo `L`. The difference
`xL - a` is taken modulo `L` and written as `xL + (L - a mod L)`, so no natural-number
subtraction truncates. The output is congruent to `a` modulo `D` for all arguments and to `xL`
modulo `L` whenever `inv * D ≡ 1 (mod L)`. Such an inverse makes `D` and `L` coprime, so
`crtCombine` reconstructs every `x < D * L` from `x mod D` and `x mod L`; Mathlib's
`Nat.chineseRemainder` gives the same value without an explicit formula.

## Main definitions

* `Cslib.crtCombine`: the explicit two-modulus recombination.

## Main results

* `Cslib.crtCombine_modEq_left`, `Cslib.crtCombine_modEq_right`: the output is congruent to `a`
  modulo `D` and, given the inverse, to `xL` modulo `L`.
* `Cslib.crtCombine_eq`: given an inverse of `D` modulo `L`, recombining `x mod D` and `x mod L`
  returns every `x < D * L`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 10.2.1, p. 374.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §16.4.3, p. 701 (step 3 of RSA-CRT inversion).
-/

public section

namespace Cslib

/-- Chinese Remainder Theorem combination of `a = x % D` and `xL = x % L` using an inverse `inv` of
`D` modulo `L`; the summand `L - a % L` represents `-a` modulo `L` without ℕ-subtraction
underflow. -/
@[expose] def crtCombine (D L a xL inv : ℕ) : ℕ :=
  a + D * ((xL + (L - a % L)) * inv % L)

/-- `crtCombine D L a xL inv` is congruent to `a` modulo `D`, for all arguments. -/
theorem crtCombine_modEq_left (D L a xL inv : ℕ) : crtCombine D L a xL inv ≡ a [MOD D] :=
  Nat.add_mul_mod_self_left a D _

/-- `crtCombine D L a xL inv` is congruent to `xL` modulo `L` when `inv * D ≡ 1 (mod L)`, for
every `a` and `xL`. -/
theorem crtCombine_modEq_right {D L inv : ℕ} (hL : 0 < L) (hinv : (inv : ZMod L) * D = 1)
    (a xL : ℕ) : crtCombine D L a xL inv ≡ xL [MOD L] := by
  have : NeZero L := ⟨hL.ne'⟩
  rw [← ZMod.natCast_eq_natCast_iff, crtCombine, Nat.cast_add, Nat.cast_mul, ZMod.natCast_mod,
    Nat.cast_mul, Nat.cast_add, ZMod.natCast_sub_mod_eq_neg]
  linear_combination ((xL : ZMod L) - a) * hinv

/-- **Chinese Remainder Theorem reconstruction** (the two-modulus case of the CRT used in
[KatzLindell2020], Section 10.2.1, p. 374): for `x < D * L`, `a = x % D`, `xL = x % L`, and
`inv * D ≡ 1 (mod L)`, `crtCombine D L a xL inv = x`. Positivity of `D` and `L` follows from
`x < D * L`, and their coprimality from the inverse. -/
theorem crtCombine_eq {D L x a xL : ℕ} (hx : x < D * L) (ha : a = x % D) (hxL : xL = x % L)
    (inv : ℕ) (hinv : (inv : ZMod L) * D = 1) :
    crtCombine D L a xL inv = x := by
  have hD : 0 < D := Nat.pos_of_ne_zero fun h => by simp [h] at hx
  have hL : 0 < L := Nat.pos_of_ne_zero fun h => by simp [h] at hx
  have hcop : Nat.Coprime D L := Nat.coprime_of_mul_modEq_one inv <| by
    rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_mul, Nat.cast_one, mul_comm]
    exact hinv
  have h1 : crtCombine D L a xL inv ≡ x [MOD D] :=
    (crtCombine_modEq_left D L a xL inv).trans (ha ▸ Nat.mod_modEq x D)
  have h2 : crtCombine D L a xL inv ≡ x [MOD L] :=
    (crtCombine_modEq_right hL hinv a xL).trans (hxL ▸ Nat.mod_modEq x L)
  have hlt : crtCombine D L a xL inv < D * L := by
    have hu : (xL + (L - a % L)) * inv % L < L := Nat.mod_lt _ hL
    have halt : a < D := ha ▸ Nat.mod_lt _ hD
    unfold crtCombine
    nlinarith
  have := (Nat.modEq_and_modEq_iff_modEq_mul hcop).1 ⟨h1, h2⟩
  rwa [Nat.ModEq, Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hx] at this

end Cslib
