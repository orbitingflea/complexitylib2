/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.PowMod
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Foundations.Algebra.Group.ZPowCoprime

/-!
# Shamir's trick: a common root from coprime exponents

Theorem 10.6 of [BonehShoup2023] (p. 416), "Shamir's trick": given a modulus `n`, relatively prime
exponents `e` and `f`, and units `w`, `y` modulo `n` with `w ^ e = y ^ f`, one can compute an `e`-th
root of `y` modulo `n` without knowing the order of `(ℤ/nℤ)ˣ`. The book's algorithm computes `s`,
`t` with `e * s + f * t = gcd(e, f) = 1` by the extended Euclidean algorithm and outputs
`x = y ^ s * w ^ t`.

`Cslib.Crypto.commonRoot n e f w y` is that algorithm on natural numbers. It takes
`s = modInv e f`, the inverse of `e` modulo `f` computed by `BinaryGcd.modInv`, and
`t = (e * s - 1) / f`, so that `e * s - f * t = 1`, and it outputs
`y ^ s * (w⁻¹) ^ t mod n` with `w⁻¹ = modInv w n`. The cases `f = 0` (which forces `e = 1`; the
output is `y mod n`) and `f = 1` (the output is `w mod n`) are separate branches: at `f = 1`,
`modInv e 1 = 0`, so the general branch would output `1`. Correctness follows from the group
identities `Commute.zpow_mul_zpow_zpow_eq_right` and `Commute.zpow_mul_zpow_zpow_eq_left` of
`CslibFrontier/Foundations/Algebra/Group/ZPowCoprime.lean`, applied in `(ZMod n)ˣ`.

## Main definitions

* `Cslib.Crypto.commonRoot`: the algorithm of Theorem 10.6 on natural numbers.

## Main results

* `Cslib.Crypto.commonRoot_pow_modEq_right`: for `0 < n`, coprime `e` and `f`, `w` coprime to `n`
  and `w ^ e ≡ y ^ f [MOD n]`, the output `x` satisfies `x ^ e ≡ y [MOD n]`.
* `Cslib.Crypto.commonRoot_pow_modEq_left`: under the same hypotheses, `x ^ f ≡ w [MOD n]`.
* `Cslib.Crypto.commonRoot_coprime`: if moreover `y` is coprime to `n`, the output is coprime to
  `n`, so it is a unit modulo `n` as in the book.
* `Cslib.Crypto.commonRoot_lt`: for `0 < n`, the output is below `n`.
* `Cslib.Crypto.computableInPolyTime_commonRoot`: `commonRoot` is computable in polynomial time
  from polynomial-time inputs on `encNat`, with no condition on the inputs.

## Implementation notes

The statement differs from the book's in three ways.

* The exponents `e` and `f` are natural numbers. The book allows negative exponents, and its proof
  of Theorem 10.7 (p. 417) applies the theorem with `f = b' - b`. Signed inputs are left to that
  first caller; the identities in `ZPowCoprime.lean` already take integer exponents.
* One output `x` is both an `e`-th root of `y` and an `f`-th root of `w`. The book's theorem states
  only the first. Section 10.9 (pp. 422–423) applies the theorem to aggregate two membership
  proofs, and recovering each proof from the aggregate (p. 422) is the second.
* The book takes a positive `n` and units `w`, `y` modulo `n`. Here `w` and `y` are natural
  numbers, not necessarily below `n`, and the two congruences assume only that `w` is coprime to
  `n`: for `f ≠ 0` this makes `y` coprime to `n`, and for `f = 0` they do not need it.
  `commonRoot_coprime`, the book's `x ∈ ℤₙ*`, also assumes that `y` is coprime to `n`, and uses
  this only when `f = 0`.

The certificate covers the computation on encoded numbers. Nothing here concerns an adversary or
a security game. Theorem 10.5 is in `RSAUnitInversion.lean`; Theorem 10.7 and the accumulator of
§10.9 are not formalized.

The common-modulus attack on plain RSA is this program on two ciphertexts:
`Cslib.Crypto.commonRoot_rsaEval` in `RSAAttacks.lean` proves that for coprime `e₁`, `e₂` and `m`
coprime to `N`, `commonRoot N e₂ e₁ (rsaEval N e₁ m) (rsaEval N e₂ m) = m % N`, and
`computableInPolyTime_commonRoot` is the attack's polynomial-time certificate.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  §10.6.2, Theorem 10.6, p. 416.
-/

public section

namespace Cslib.Crypto

open Turing.MultiTapeTM

/-- The algorithm of [BonehShoup2023], Theorem 10.6 (Shamir's trick), on natural numbers. For a
modulus `n`, exponents `e`, `f` and residues `w`, `y`, it returns `y mod n` when `f = 0`, `w mod n`
when `f = 1`, and otherwise `y ^ s * (w⁻¹) ^ t mod n`, where `s = modInv e f`,
`t = (e * s - 1) / f` and `w⁻¹ = modInv w n`. When `0 < n`, `e` and `f` are coprime, `w` is coprime
to `n` and `w ^ e ≡ y ^ f [MOD n]`, the output is an `e`-th root of `y` and an `f`-th root of `w`
modulo `n` (`commonRoot_pow_modEq_right`, `commonRoot_pow_modEq_left`), and a unit modulo `n` if
`y` is also coprime to `n` (`commonRoot_coprime`). -/
@[expose] def commonRoot (n e f w y : ℕ) : ℕ :=
  if f = 0 then y % n
  else if f = 1 then w % n
  else powMod n y (BinaryGcd.modInv e f) *
    powMod n (BinaryGcd.modInv w n) ((e * BinaryGcd.modInv e f - 1) / f) % n

/-- The output of `commonRoot` is below a positive modulus. -/
theorem commonRoot_lt {n : ℕ} (hn : 0 < n) (e f w y : ℕ) : commonRoot n e f w y < n := by
  unfold commonRoot
  split_ifs <;> exact Nat.mod_lt _ hn

/-- For `2 ≤ f` and `e` coprime to `f`, `s = modInv e f` and `t = (e * s - 1) / f` satisfy
`e * s = f * t + 1`. -/
private theorem mul_modInv_eq_mul_div_add_one {e f : ℕ} (hf : 2 ≤ f) (hef : Nat.Coprime e f) :
    e * BinaryGcd.modInv e f = f * ((e * BinaryGcd.modInv e f - 1) / f) + 1 := by
  have hmod : e * BinaryGcd.modInv e f % f = 1 :=
    Eq.trans (BinaryGcd.mul_modInv_modEq_one (by omega) hef) (Nat.mod_eq_of_lt (by omega))
  have hdiv := Nat.div_add_mod (e * BinaryGcd.modInv e f) f
  generalize e * BinaryGcd.modInv e f = k at hmod hdiv ⊢
  have hk : k - 1 = f * (k / f) := by omega
  rw [hk, Nat.mul_div_cancel_left _ (by omega)]
  omega

/-- When `f ≠ 0`, `w` is coprime to `n` and `w ^ e ≡ y ^ f [MOD n]`, `y` is coprime to `n`. -/
private theorem coprime_of_pow_modEq_pow {n e f w y : ℕ} (hf : f ≠ 0) (hw : Nat.Coprime w n)
    (h : w ^ e ≡ y ^ f [MOD n]) : Nat.Coprime y n := by
  have hyf : Nat.Coprime (y ^ f) n := by
    rw [Nat.Coprime, ← h.gcd_eq]
    exact Nat.Coprime.pow_left e hw
  exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hf) y n).mp hyf

/-- For `f ≠ 0`, the output of `commonRoot` is `Y ^ s * W ^ t` in `(ZMod n)ˣ` for the units `W`
and `Y` of `w` and `y` and some `e * s + f * t = 1`. -/
private theorem natCast_commonRoot {n e f w y : ℕ} (hn : 0 < n) (hf : f ≠ 0)
    (hef : Nat.Coprime e f) (hw : Nat.Coprime w n) (hy : Nat.Coprime y n) :
    ∃ s t : ℤ, (e : ℤ) * s + f * t = 1 ∧ (commonRoot n e f w y : ZMod n) =
      ((ZMod.unitOfCoprime y hy ^ s * ZMod.unitOfCoprime w hw ^ t : (ZMod n)ˣ) : ZMod n) := by
  by_cases hf1 : f = 1
  · refine ⟨0, 1, by simp [hf1], ?_⟩
    simp [commonRoot, hf1]
  · have hf2 : 2 ≤ f := by omega
    have hbez := mul_modInv_eq_mul_div_add_one hf2 hef
    refine ⟨BinaryGcd.modInv e f, -(((e * BinaryGcd.modInv e f - 1) / f : ℕ) : ℤ), ?_, ?_⟩
    · generalize (e * BinaryGcd.modInv e f - 1) / f = t at hbez ⊢
      have hbez' : (e : ℤ) * BinaryGcd.modInv e f = f * t + 1 := by exact_mod_cast hbez
      linarith
    · have hinv : ((ZMod.unitOfCoprime w hw)⁻¹ : (ZMod n)ˣ) = (BinaryGcd.modInv w n : ZMod n) := by
        apply Units.inv_eq_of_mul_eq_one_right
        rw [ZMod.coe_unitOfCoprime, ← Nat.cast_mul, ← Nat.cast_one,
          ZMod.natCast_eq_natCast_iff]
        exact BinaryGcd.mul_modInv_modEq_one hn hw
      simp only [commonRoot, hf, hf1, ↓reduceIte, powMod_of_ne_zero hn.ne', Nat.cast_mul,
        ZMod.natCast_mod, Nat.cast_pow, zpow_neg, zpow_natCast, Units.val_mul,
        Units.val_pow_eq_pow_val, ← inv_pow, hinv, ZMod.coe_unitOfCoprime]

/-- The two congruences of `commonRoot`, proved together. -/
private theorem commonRoot_pow_modEq {n e f w y : ℕ} (hn : 0 < n) (hef : Nat.Coprime e f)
    (hw : Nat.Coprime w n) (h : w ^ e ≡ y ^ f [MOD n]) :
    commonRoot n e f w y ^ e ≡ y [MOD n] ∧ commonRoot n e f w y ^ f ≡ w [MOD n] := by
  by_cases hf : f = 0
  · subst hf
    obtain rfl : e = 1 := Nat.coprime_zero_right e |>.mp hef
    simp only [commonRoot, ↓reduceIte, pow_one, pow_zero] at h ⊢
    exact ⟨Nat.mod_modEq y n, h.symm⟩
  · have hy := coprime_of_pow_modEq_pow hf hw h
    obtain ⟨s, t, hst, hx⟩ := natCast_commonRoot hn hf hef hw hy
    set W := ZMod.unitOfCoprime w hw
    set Y := ZMod.unitOfCoprime y hy
    have hWY : W ^ (e : ℤ) = Y ^ (f : ℤ) := by
      ext
      simp only [zpow_natCast, Units.val_pow_eq_pow_val, W, Y, ZMod.coe_unitOfCoprime,
        ← Nat.cast_pow]
      exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h
    have hright := (Commute.all W Y).zpow_mul_zpow_zpow_eq_right hst hWY
    have hleft := (Commute.all W Y).zpow_mul_zpow_zpow_eq_left hst hWY
    constructor
    · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hx, ← Units.val_pow_eq_pow_val,
        ← zpow_natCast, hright, ZMod.coe_unitOfCoprime]
    · rw [← ZMod.natCast_eq_natCast_iff, Nat.cast_pow, hx, ← Units.val_pow_eq_pow_val,
        ← zpow_natCast, hleft, ZMod.coe_unitOfCoprime]

/-- **Shamir's trick** ([BonehShoup2023], Theorem 10.6, p. 416). For `0 < n`, coprime `e` and `f`,
`w` coprime to `n` and `w ^ e ≡ y ^ f [MOD n]`, the output `x = commonRoot n e f w y` satisfies
`x ^ e ≡ y [MOD n]`. The book's exponents are integers; here they are natural numbers. -/
theorem commonRoot_pow_modEq_right {n e f w y : ℕ} (hn : 0 < n) (hef : Nat.Coprime e f)
    (hw : Nat.Coprime w n) (h : w ^ e ≡ y ^ f [MOD n]) :
    commonRoot n e f w y ^ e ≡ y [MOD n] :=
  (commonRoot_pow_modEq hn hef hw h).1

/-- The output of Shamir's trick is also an `f`-th root of `w`: for `0 < n`, coprime `e` and `f`,
`w` coprime to `n` and `w ^ e ≡ y ^ f [MOD n]`, `commonRoot n e f w y ^ f ≡ w [MOD n]`. The book's
Theorem 10.6 does not state this; §10.9 (p. 422) uses it to split an aggregated membership
proof. -/
theorem commonRoot_pow_modEq_left {n e f w y : ℕ} (hn : 0 < n) (hef : Nat.Coprime e f)
    (hw : Nat.Coprime w n) (h : w ^ e ≡ y ^ f [MOD n]) :
    commonRoot n e f w y ^ f ≡ w [MOD n] :=
  (commonRoot_pow_modEq hn hef hw h).2

/-- The output of Shamir's trick is a unit modulo `n`, as in [BonehShoup2023], Theorem 10.6
(`x ∈ ℤₙ*`): for `0 < n`, coprime `e` and `f`, `w` and `y` coprime to `n` and
`w ^ e ≡ y ^ f [MOD n]`, `commonRoot n e f w y` is coprime to `n`. The hypothesis on `y` is used
only when `f = 0`, where the output is `y mod n`. -/
theorem commonRoot_coprime {n e f w y : ℕ} (hn : 0 < n) (hef : Nat.Coprime e f)
    (hw : Nat.Coprime w n) (hy : Nat.Coprime y n) (h : w ^ e ≡ y ^ f [MOD n]) :
    Nat.Coprime (commonRoot n e f w y) n := by
  by_cases hf : f = 0
  · have he : e = 1 := Nat.coprime_zero_right e |>.mp (hf ▸ hef)
    have hx : Nat.Coprime (commonRoot n e f w y ^ e) n :=
      (commonRoot_pow_modEq_right hn hef hw h).gcd_eq.trans hy
    exact (Nat.coprime_pow_left_iff (by omega) _ _).mp hx
  · have hx : Nat.Coprime (commonRoot n e f w y ^ f) n :=
      (commonRoot_pow_modEq_left hn hef hw h).gcd_eq.trans hw
    exact (Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero hf) _ _).mp hx

/-- `commonRoot` is computable in polynomial time whenever `n`, `e`, `f`, `w` and `y` are
computable in polynomial time as natural numbers on `encNat`. There is no condition on the
inputs: the modular exponentiations use `powMod`, which returns `1` at the modulus `0`. -/
theorem computableInPolyTime_commonRoot {α : Type} {enc : α ↪ List Bool} {n e f w y : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hf : ComputableInPolyTime f enc encNat) (hw : ComputableInPolyTime w enc encNat)
    (hy : ComputableInPolyTime y enc encNat) :
    ComputableInPolyTime (fun a => commonRoot (n a) (e a) (f a) (w a) (y a)) enc encNat := by
  have hs := ComputableInPolyTime.binary_modInv' he hf
  have ht := ComputableInPolyTime.binary_div'
    (ComputableInPolyTime.binary_sub' (ComputableInPolyTime.binary_mul' he hs)
      (ComputableInPolyTime.const 1)) hf
  have hroot := ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul' (computableInPolyTime_powMod hn hy hs)
      (computableInPolyTime_powMod hn (ComputableInPolyTime.binary_modInv' hw hn) ht)) hn
  unfold commonRoot
  exact ComputableInPolyTime.ite_decide
    (ComputableInPolyTime.decide_eq' hf (ComputableInPolyTime.const 0))
    (ComputableInPolyTime.binary_mod' hy hn)
    (ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.decide_eq' hf (ComputableInPolyTime.const 1))
      (ComputableInPolyTime.binary_mod' hw hn) hroot)

end Cslib.Crypto
