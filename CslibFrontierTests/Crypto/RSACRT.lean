/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RSACRT
import Mathlib.Tactic.NormNum.Prime

/-!
# RSA-CRT inversion and the fault-attack gcd identity: checked instances

Concrete checks for `CslibFrontier/Crypto/Computational/RSACRT.lean`:

* For the key `p = 61`, `q = 53`, `e = 17`, `d = 2753` with `q_inv = 38`, RSA-CRT inversion
  agrees with `rsaInvert 3233 2753` on several inputs, including multiples of `p` and of `q`, and
  `invert_crtKeyWith` and `invert_crtKey` apply to every input. `crtQInv_eq_zmod_inv_val` gives
  `crtQInv = 38`.
* Recombining the correct `x_q` with the faulty `x_p' = 40` (the correct value is `39`) for
  `h = 65` gives `σ = 2602` and `gcd(σ ^ 17 − 65 mod 3233, 3233) = 53 = q`, both by evaluation and
  by `gcd_val_pow_sub_combine_eq_q`, which `crtKey_eq_crtKeyWith` also transfers to `crtKey`.
  With the correct `x_p` the gcd is `3233`, so the hypothesis that `x_p'` is wrong is needed.
* The hypotheses `p ≠ 2` and `q ≠ 2` of `invert_crtKeyWith` are needed: for `p = 2`, `q = 5`,
  `e = d = 3` and `y = 2`, RSA-CRT returns `3` while `y ^ d mod n = 8`.
* The polynomial-time certificates `computableInPolyTime_crtInvert`,
  `computableInPolyTime_crtKeyWith_invert`, `computableInPolyTime_crtQInv`,
  `computableInPolyTime_crtKey_invert` and `computableInPolyTime_gcd_val_pow_sub` apply to fixed
  keys and moduli, with the remaining argument read from `encNat`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSACRT

open Cslib.Crypto

/-! ### The key `p = 61`, `q = 53` -/

/-- The key `p = 61`, `q = 53`, `e = 17`, `d = 2753`: `17 * 2753 = 15 * 3120 + 1`. -/
def rsa3233 : RSADesc :=
  { p := 61, q := 53, e := 17, d := 2753, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- `38` is an inverse of `53` modulo `61`: `38 * 53 = 2014 = 33 * 61 + 1`. -/
theorem qInv_3233 : 38 * rsa3233.q ≡ 1 [MOD rsa3233.p] := by decide

/-- The key derived from `rsa3233`: `d_p = 2753 mod 60 = 53` and `d_q = 2753 mod 52 = 49`. -/
example : rsa3233.crtKeyWith 38 = ⟨61, 53, 53, 49, 38⟩ := rfl

/-- `crtQInv` is `38` for this key, computed through `crtQInv_eq_zmod_inv_val`. -/
example : rsa3233.crtQInv = 38 := by
  rw [RSADesc.crtQInv_eq_zmod_inv_val]
  change ((53 : ℕ) : ZMod 61)⁻¹.val = 38
  rw [ZMod.inv_eq_of_mul_eq_one 61 _ 38 (by decide)]
  rfl

/-- RSA-CRT inversion agrees with `y ^ d mod n` on units, on `0` and `n - 1`, and on the
multiples `53` and `61` of the prime factors. -/
example :
    [0, 1, 2, 65, 1000, 3232, 53, 61].map (rsa3233.crtKeyWith 38).invert =
      [0, 1, 1027, 588, 2951, 3232, 3074, 2806] ∧
    [0, 1, 2, 65, 1000, 3232, 53, 61].map (rsaInvert 3233 2753) =
      [0, 1, 1027, 588, 2951, 3232, 3074, 2806] := by
  decide +kernel

/-- The intermediate values for `y = 65`: `x_p = 39`, `x_q = 5`, and their recombination. -/
example : (rsa3233.crtKeyWith 38).powP 65 = 39 ∧ (rsa3233.crtKeyWith 38).powQ 65 = 5 ∧
    (rsa3233.crtKeyWith 38).combine 39 5 = 588 := by
  decide

/-- `invert_crtKeyWith` applies to every input. -/
example (y : ℕ) : (rsa3233.crtKeyWith 38).invert y = rsaInvert 3233 2753 y :=
  rsa3233.invert_crtKeyWith (by decide) (by decide) qInv_3233 y

/-- `invert_crtKey` applies to every input. -/
example (y : ℕ) : rsa3233.crtKey.invert y = rsaInvert 3233 2753 y :=
  rsa3233.invert_crtKey (by decide) (by decide) y

/-! ### The fault-attack gcd identity -/

/-- A faulty `x_p' = 40` recombined with the correct `x_q = 5` gives `σ = 2602`, and
`σ ^ 17 − 65` in `[0, 3233)` is `1431 = 27 * 53`, whose gcd with `3233` is `q = 53`. -/
example : (rsa3233.crtKeyWith 38).combine 40 5 = 2602 ∧
    (((2602 : ℕ) : ZMod 3233) ^ 17 - ((65 : ℕ) : ZMod 3233)).val = 1431 ∧
    Nat.gcd 1431 3233 = 53 := by
  decide

/-- `gcd_val_pow_sub_combine_eq_q` on the faulty value `x_p' = 40` and the correct
`x_q = 5 ≡ 65 ^ 2753 (mod 53)`, for `h = 65`. -/
example :
    Nat.gcd ((((rsa3233.crtKeyWith 38).combine 40 5 : ℕ) : ZMod 3233) ^ 17 -
      ((65 : ℕ) : ZMod 3233)).val 3233 = 53 :=
  rsa3233.gcd_val_pow_sub_combine_eq_q qInv_3233 (by decide +kernel) (by decide +kernel)

/-- `crtKey_eq_crtKeyWith` transfers `gcd_val_pow_sub_combine_eq_q` to `crtKey`: recombining the
faulty `x_p' = 40` with the correct `x_q = 5` under `rsa3233.crtKey` also gives the gcd `q = 53`. -/
example :
    Nat.gcd (((rsa3233.crtKey.combine 40 5 : ℕ) : ZMod 3233) ^ 17 - ((65 : ℕ) : ZMod 3233)).val
      3233 = 53 := by
  rw [RSADesc.crtKey_eq_crtKeyWith]
  exact rsa3233.gcd_val_pow_sub_combine_eq_q rsa3233.crtQInv_mul_modEq_one (by decide +kernel)
    (by decide +kernel)

/-- `gcd_val_pow_sub_eq_q` on `σ = 2602` and `h = 65`. -/
example : Nat.gcd (((2602 : ℕ) : ZMod 3233) ^ 17 - ((65 : ℕ) : ZMod 3233)).val 3233 = 53 :=
  rsa3233.gcd_val_pow_sub_eq_q (by decide +kernel) (by decide +kernel)

/-- With the correct `x_p = 39` the output is the correct value `rsaInvert 3233 2753 65 = 588`,
`σ ^ 17 − 65` is `0` and the gcd is `n`: the fault on `x_p` is needed. -/
example : Nat.gcd ((((rsa3233.crtKeyWith 38).combine 39 5 : ℕ) : ZMod 3233) ^ 17 -
    ((65 : ℕ) : ZMod 3233)).val 3233 = 3233 := by
  decide

/-! ### Oddness is needed -/

/-- The key `p = 2`, `q = 5`, `e = d = 3`: `3 * 3 = 2 * 4 + 1`. -/
def rsa10 : RSADesc :=
  { p := 2, q := 5, e := 3, d := 3, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- For `p = 2` the exponent `d_p = 3 mod 1` is `0`, so step 1 returns `1`; with the inverse
`q_inv = 1` of `5` modulo `2`, RSA-CRT inversion of `2` returns `3`, while `2 ^ 3 mod 10 = 8`. -/
example : 1 * rsa10.q ≡ 1 [MOD rsa10.p] ∧ (rsa10.crtKeyWith 1).dp = 0 ∧
    (rsa10.crtKeyWith 1).invert 2 = 3 ∧ rsaInvert rsa10.modulus rsa10.d 2 = 8 := by
  decide

/-- The conclusion of `invert_crtKeyWith` fails without `p ≠ 2`. -/
example : ¬ ∀ y, (rsa10.crtKeyWith 1).invert y = rsaInvert rsa10.modulus rsa10.d y :=
  fun h => absurd (h 2) (by decide)

/-! ### Polynomial-time certificates -/

section PolyTime

open Turing.MultiTapeTM

/-- `computableInPolyTime_crtInvert` for the fixed key `(61, 53, 53, 49, 38)`, with the input
read from `encNat`. -/
example : ComputableInPolyTime
    (fun y => ({ p := 61, q := 53, dp := 53, dq := 49, qInv := 38 } : RSACRTKey).invert y)
    encNat encNat :=
  computableInPolyTime_crtInvert (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (fun _ => by norm_num) (fun _ => by norm_num)

/-- `computableInPolyTime_crtKeyWith_invert` for the fixed key `rsa3233.crtKeyWith 38`, with the
input read from `encNat`. -/
example : ComputableInPolyTime (fun y => (rsa3233.crtKeyWith 38).invert y) encNat encNat :=
  computableInPolyTime_crtKeyWith_invert (desc := fun _ => rsa3233) (qInv := fun _ => 38)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_crtQInv` for the fixed key `rsa3233`, with the input read from
`encNat`. -/
example : ComputableInPolyTime (fun _ : ℕ => rsa3233.crtQInv) encNat encNat :=
  computableInPolyTime_crtQInv (desc := fun _ => rsa3233) (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_crtKey_invert` for the fixed key `rsa3233.crtKey`, with the input read
from `encNat`. -/
example : ComputableInPolyTime (fun y => rsa3233.crtKey.invert y) encNat encNat :=
  computableInPolyTime_crtKey_invert (desc := fun _ => rsa3233) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_gcd_val_pow_sub` for `n = 3233`, `e = 17` and `h = 65`, with `σ` read
from `encNat`. -/
example : ComputableInPolyTime
    (fun σ : ℕ => Nat.gcd (((σ : ZMod 3233) ^ 17 - ((65 : ℕ) : ZMod 3233)).val) 3233)
    encNat encNat :=
  computableInPolyTime_gcd_val_pow_sub (n := fun _ => 3233) (e := fun _ => 17)
    (h := fun _ => 65) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    fun _ => by norm_num

end PolyTime

end CslibFrontierTests.Crypto.RSACRT
