/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RSAUnitInversion
import Mathlib.Tactic.NormNum.Prime

/-!
# RSA with a uniform unit preimage: checked instances

Checks for `CslibFrontier/Crypto/Computational/RSAUnitInversion.lean`:

* For `N = 33 = 3 * 11` and `e = 3`, the non-unit `6` encrypts to `18`, and `rsaNonUnitRoot`
  recovers `6` from `(33, 3, 18)` alone, as `rsaNonUnitRoot_rsaEval` says.
* `p = 2` is allowed: for `N = 10 = 2 * 5` and `e = 3`, the non-units `4` and `5` are their own
  images, and `rsaNonUnitRoot` returns them. So is `e = 1`.
* The branch `y = 0` is needed: the general branch would return `rsaInvert 33 0 0 = 1` for the
  root of `0`, since `BinaryGcd.modInv 3 0 = 0`.
* RSA evaluation keeps units and non-units apart (`coprime_rsaEval_iff`).
* Both certificates apply: `computableInPolyTime_rsaNonUnitRoot` on three inputs read as nested
  pairs on `encNat`, and `isPPT_unitRSAToRSA` on the inverter that returns its challenge.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSAUnitInversion

open Cslib Cslib.Crypto Turing.MultiTapeTM

/-- The key `N = 33`, `e = 3`, `d = 7`: `3 * 7 = 21 ≡ 1 [MOD 20]`. -/
def desc33 : RSADesc :=
  { p := 3, q := 11, e := 3, d := 7, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- A key with `p = 2`: `N = 10`, `e = 3`, `d = 3`, with `3 * 3 = 9 ≡ 1 [MOD 4]`. -/
def desc10 : RSADesc :=
  { p := 2, q := 5, e := 3, d := 3, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- A key with `e = 1`: `N = 10`, `e = d = 1`. -/
def desc10One : RSADesc :=
  { p := 2, q := 5, e := 1, d := 1, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-! ### The root of a non-unit -/

/-- `6 ^ 3 = 216 ≡ 18 [MOD 33]`; `gcd 18 33 = 3`, so the exponent is the inverse `7` of `3`
modulo `(3 - 1) * (11 - 1) = 20`, and `18 ^ 7 ≡ 6 [MOD 33]`. -/
example : rsaEval 33 3 6 = 18 := by decide

example : rsaNonUnitRoot 33 3 18 = 6 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 (rsaEval 33 3 6) = 6 :=
  rsaNonUnitRoot_rsaEval desc33 (x := 6) (by decide) (by decide)

/-- With `p = 2`: `4 ^ 3 ≡ 4` and `5 ^ 3 ≡ 5 [MOD 10]`, and the roots are `4` and `5`. -/
example : rsaEval 10 3 4 = 4 ∧ rsaEval 10 3 5 = 5 := by decide

example : rsaNonUnitRoot 10 3 4 = 4 ∧ rsaNonUnitRoot 10 3 5 = 5 := by
  unfold rsaNonUnitRoot BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 10 3 (rsaEval 10 3 4) = 4 :=
  rsaNonUnitRoot_rsaEval desc10 (x := 4) (by decide) (by decide)

/-- With `e = 1`, RSA evaluation is the identity and so is the root. -/
example : rsaNonUnitRoot 10 1 (rsaEval 10 1 6) = 6 :=
  rsaNonUnitRoot_rsaEval desc10One (x := 6) (by decide) (by decide)

/-- The branch `y = 0` is needed: `BinaryGcd.modInv 3 0 = 0`, and `0 ^ 0 % 33 = 1`. -/
example : BinaryGcd.modInv 3 ((Nat.gcd 0 33 - 1) * (33 / Nat.gcd 0 33 - 1)) = 0 ∧
    rsaInvert 33 0 0 = 1 := by
  unfold BinaryGcd.modInv
  decide

example : rsaNonUnitRoot 33 3 (rsaEval 33 3 0) = 0 :=
  rsaNonUnitRoot_rsaEval desc33 (x := 0) (by decide) (by decide)

/-! ### Units and non-units -/

/-- `5` is a unit modulo `33` and so is its image `5 ^ 3 % 33 = 26`; `6` is not, nor is `18`. -/
example : Nat.Coprime (rsaEval 33 3 5) 33 ∧ ¬ Nat.Coprime (rsaEval 33 3 6) 33 :=
  ⟨(coprime_rsaEval_iff desc33 5).mpr (by decide),
    fun h => absurd ((coprime_rsaEval_iff desc33 6).mp h) (by decide)⟩

/-! ### Certificates -/

example : ComputableInPolyTime
    (fun a : ℕ × ℕ × ℕ => rsaNonUnitRoot (a.1 + 1) a.2.1 a.2.2)
    (encPair encNat (encPair encNat encNat)) encNat :=
  computableInPolyTime_rsaNonUnitRoot (by fun_prop) (by fun_prop) (by fun_prop)
    fun _ => Nat.succ_pos _

/-- The inverter that returns its challenge. -/
noncomputable def echo : RSAInverter := fun _ _ y => pure y

theorem isPPT_echo : echo.IsPPT :=
  ((ComputableInPolyTime.isPPTOn (f := fun x : RSAInput => (x.challenge : ℕ))
    (by fun_prop))).congr fun _ => by simp [echo]

example : (unitRSAToRSA echo).IsPPT := isPPT_unitRSAToRSA isPPT_echo

end CslibFrontierTests.Crypto.RSAUnitInversion
