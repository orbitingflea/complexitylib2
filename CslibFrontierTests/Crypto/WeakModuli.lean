/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.Factoring.WeakModuli
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Prime

/-!
# Weak RSA moduli: checked instances

Concrete checks for `CslibFrontier/Crypto/Computational/Factoring/WeakModuli.lean`
([BonehShoup2023], Section 16.4.2, pp. 698–699):

* The moduli `101 * 103` and `101 * 107` share the prime `101`, and their gcd finds it; with
  equal second primes the gcd is the whole modulus.
* `10403 = 101 * 103` satisfies the closeness bound, so `⌈√10403⌉ = 102` and `fermatFactor`
  returns `(103, 101)`, both by evaluation and by `fermatFactor_mul_eq`.
* `303 = 3 * 101` violates the closeness bound, and `fermatFactor`, which tries only
  `A = ⌈√303⌉ = 18`, returns `(22, 13)`. Fermat's full method, which goes on to larger `A`,
  would factor `303` at `A = 52`, where `52 ^ 2 - 303 = 49 ^ 2`.
* For `6 = 3 * 2` the closeness bound holds but `3 + 2` is odd: `⌈√6⌉ = 3 ≠ (3 + 2) / 2`, and
  `fermatFactor` returns `(4, 1)`, so the parity hypothesis is needed.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.WeakModuli

open Cslib Cslib.Crypto

/-- RSA key with `n = 101 * 103 = 10403`, `e = 7`, `d = 8743` (`7 * 8743 = 6 * 10200 + 1`). -/
def rsa10403 : RSADesc :=
  { p := 101, q := 103, e := 7, d := 8743, hp := by norm_num, hq := by norm_num,
    hpq := by decide, he := by decide, hed := by decide }

/-- RSA key with `n = 101 * 107 = 10807`, sharing the prime `101` with `rsa10403`; `e = 7`,
`d = 4543` (`7 * 4543 = 3 * 10600 + 1`). -/
def rsa10807 : RSADesc :=
  { p := 101, q := 107, e := 7, d := 4543, hp := by norm_num, hq := by norm_num,
    hpq := by decide, he := by decide, hed := by decide }

/-! ### Shared primes -/

example : Nat.gcd (101 * 103) (101 * 107) = 101 :=
  gcd_mul_mul_of_prime_ne (by norm_num) (by norm_num) (by decide)

/-- The two published moduli reveal their common prime. -/
example : Nat.gcd rsa10403.modulus rsa10807.modulus = 101 :=
  RSADesc.gcd_modulus_eq_of_p_eq rsa10403 rsa10807 rfl (by decide)

example : rsa10403.modulus = 10403 ∧ rsa10807.modulus = 10807 := by decide

/-- With equal second primes the gcd is the whole modulus, not the shared prime. -/
example : Nat.gcd (101 * 103) (101 * 103) ≠ 101 := by decide

/-! ### Close primes: `10403 = 101 * 103` -/

/-- The closeness bound for `p = 103`, `q = 101`, checked through its polynomial form
`2 ^ 4 < 16 * 10403`. -/
theorem close_103_101 :
    |((103 : ℕ) : ℝ) - (101 : ℕ)| < 2 * (((103 : ℕ) : ℝ) * (101 : ℕ)) ^ (1 / 4 : ℝ) :=
  (abs_sub_lt_two_mul_rpow_iff (by positivity)).2 (by norm_num)

/-- Lemma 16.4 at `p = 103`, `q = 101`: `|102 - √10403| < 1 / 2`. -/
example : |((103 : ℝ) + 101) / 2 - Real.sqrt (103 * 101)| < 1 / 2 :=
  abs_add_div_two_sub_sqrt_mul_lt_half (by norm_num) (by norm_num)
    ((abs_sub_lt_two_mul_rpow_iff (by norm_num)).2 (by norm_num))

example : (if 103 * 101 = 0 then 0 else (103 * 101 - 1).sqrt + 1) = (103 + 101) / 2 :=
  ceilSqrt_mul_eq_add_div_two (by decide) close_103_101

/-- The natural-number ceiling square root agrees with the real ceiling here: `⌈√10403⌉ = 102`,
since `101 ^ 2 < 10403 ≤ 102 ^ 2`. -/
example : ⌈Real.sqrt 10403⌉₊ = 102 := by
  rw [Nat.ceil_eq_iff (by norm_num), Real.lt_sqrt (by norm_num), Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `fermatFactor` factors `10403`, by evaluation. -/
example : fermatFactor 10403 = (103, 101) := by
  norm_num [fermatFactor, factorOfTotient]

/-- `fermatFactor` factors `10403`, from `fermatFactor_mul_eq`. -/
example : fermatFactor (103 * 101) = (103, 101) :=
  fermatFactor_mul_eq (by norm_num) (by decide) close_103_101

/-- `fermatFactor` factors the RSA modulus of `rsa10403`. -/
example : fermatFactor rsa10403.modulus = (103, 101) :=
  RSADesc.fermatFactor_eq rsa10403 (by decide) (by decide)
    ((abs_sub_lt_two_mul_rpow_iff (by positivity)).2 (by norm_num [rsa10403]))

/-! ### Distant primes: `303 = 3 * 101` -/

/-- `3` and `101` are far apart: `98 ^ 4 ≥ 16 * 303`. -/
example : ¬ |((101 : ℕ) : ℝ) - (3 : ℕ)| < 2 * (((101 : ℕ) : ℝ) * (3 : ℕ)) ^ (1 / 4 : ℝ) := by
  rw [abs_sub_lt_two_mul_rpow_iff (by positivity)]
  norm_num

/-- The single step `A = ⌈√303⌉ = 18` of `fermatFactor` does not factor `303 = 3 * 101`; Fermat's
full method would continue to `A = 52`. -/
example : fermatFactor 303 = (22, 13) := by
  norm_num [fermatFactor, factorOfTotient]

/-! ### Parity: `6 = 3 * 2` -/

/-- `3` and `2` are close: `1 ^ 4 < 16 * 6`. -/
example : |((3 : ℕ) : ℝ) - (2 : ℕ)| < 2 * (((3 : ℕ) : ℝ) * (2 : ℕ)) ^ (1 / 4 : ℝ) :=
  (abs_sub_lt_two_mul_rpow_iff (by positivity)).2 (by norm_num)

/-- With `p + q = 5` odd, `⌈√6⌉ = 3` is not `(3 + 2) / 2 = 2`. -/
example : (if 3 * 2 = 0 then 0 else (3 * 2 - 1).sqrt + 1) ≠ (3 + 2) / 2 := by
  norm_num

/-- `fermatFactor` does not factor `6 = 3 * 2`. -/
example : fermatFactor 6 = (4, 1) := by
  norm_num [fermatFactor, factorOfTotient]

end CslibFrontierTests.Crypto.WeakModuli
