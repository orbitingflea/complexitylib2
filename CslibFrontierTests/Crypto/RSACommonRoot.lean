/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RSACommonRoot

/-!
# Shamir's trick: checked instances

Checks for `CslibFrontier/Crypto/Computational/RSACommonRoot.lean`:

* The book's warm-up `e = 3`, `f = 2` modulo `35`, with `w = 4`, `y = 8`: `commonRoot` returns `2`,
  and the correctness theorems apply, including `commonRoot_coprime`. A second instance, `e = 3`,
  `f = 5`, `w = 32`, `y = 8`, uses the coefficient `t = 1` on the inverse of `w`.
* The branch `f = 1` returns `w`; the general branch would return `1` there. The branch `f = 0`
  forces `e = 1` and returns `y`, which need not be a unit; then the output is not a unit either.
* The hypotheses are needed: for `e = f = 2` modulo `3`, and for a `w` that is not a unit modulo
  `8`, `w ^ e ≡ y ^ f` holds and `y` has no `e`-th root at all.
* The polynomial-time certificate applies to all five inputs read as nested pairs on `encNat`, and
  to fixed `n`, `e`, `f`, `w`, with `y` read from `encNat`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSACommonRoot

open Cslib.Crypto Turing.MultiTapeTM

/-! ### Instances -/

/-- The warm-up: `4 ^ 3 ≡ 8 ^ 2 [MOD 35]` (both are `29`), and the cube root of `8` is `2`:
`s = modInv 3 2 = 1`, `t = 1`, and `8 * modInv 4 35 = 8 * 9 ≡ 2`. -/
example : commonRoot 35 3 2 4 8 = 2 := by
  unfold commonRoot BinaryGcd.modInv
  decide

example : commonRoot 35 3 2 4 8 ^ 3 ≡ 8 [MOD 35] :=
  commonRoot_pow_modEq_right (by norm_num) (by decide) (by decide) (by decide)

example : commonRoot 35 3 2 4 8 ^ 2 ≡ 4 [MOD 35] :=
  commonRoot_pow_modEq_left (by norm_num) (by decide) (by decide) (by decide)

/-- The output is a unit modulo `35`, as the book's `x ∈ ℤₙ*`. -/
example : Nat.Coprime (commonRoot 35 3 2 4 8) 35 :=
  commonRoot_coprime (by norm_num) (by decide) (by decide) (by decide) (by decide)

/-- `32 ^ 3 ≡ 8 ^ 5 [MOD 35]`, with `s = modInv 3 5 = 2` and `t = (3 * 2 - 1) / 5 = 1`: the output
is `8 ^ 2 * 32⁻¹ = 64 * 23 ≡ 2`. -/
example : commonRoot 35 3 5 32 8 = 2 := by
  unfold commonRoot BinaryGcd.modInv
  decide

example : commonRoot 35 3 5 32 8 < 35 := commonRoot_lt (by norm_num) _ _ _ _

/-! ### The cases `f = 1` and `f = 0` -/

/-- For `f = 1` the output is `w`: `4 ^ 3 ≡ 29 [MOD 35]`. -/
example : commonRoot 35 3 1 4 29 = 4 := by decide

example : commonRoot 35 3 1 4 29 ^ 3 ≡ 29 [MOD 35] :=
  commonRoot_pow_modEq_right (by norm_num) (by decide) (by decide) (by decide)

/-- The general branch is wrong at `f = 1`: `modInv 3 1 = 0`, so `t = 0` and it returns `1`. -/
example : powMod 35 29 (BinaryGcd.modInv 3 1) *
    powMod 35 (BinaryGcd.modInv 4 35) ((3 * BinaryGcd.modInv 3 1 - 1) / 1) % 35 = 1 := by
  unfold BinaryGcd.modInv
  decide

/-- For `f = 0`, coprimality forces `e = 1`, and the output is `y`. Here `y = 2` is not a unit
modulo `4`; the theorems do not need it to be. -/
example : commonRoot 4 1 0 1 2 = 2 := by decide

example : commonRoot 4 1 0 1 2 ^ 1 ≡ 2 [MOD 4] ∧ commonRoot 4 1 0 1 2 ^ 0 ≡ 1 [MOD 4] :=
  ⟨commonRoot_pow_modEq_right (by norm_num) (by decide) (by decide) (by decide),
    commonRoot_pow_modEq_left (by norm_num) (by decide) (by decide) (by decide)⟩

/-- The output `2` is not a unit modulo `4`, so `commonRoot_coprime` needs `y` coprime to `n` at
`f = 0`. -/
example : ¬ Nat.Coprime (commonRoot 4 1 0 1 2) 4 := by decide

/-! ### The hypotheses are needed -/

/-- Coprime exponents: `1 ^ 2 ≡ 2 ^ 2 [MOD 3]`, but `2` is not a square modulo `3`, so no output
can be a square root of `y = 2`. -/
example : 1 ^ 2 ≡ 2 ^ 2 [MOD 3] ∧ (∀ x : ZMod 3, x ^ 2 ≠ 2) ∧
    ¬ commonRoot 3 2 2 1 2 ^ 2 ≡ 2 [MOD 3] := by
  refine ⟨by decide, by decide, ?_⟩
  unfold commonRoot BinaryGcd.modInv
  decide

/-- A unit `w`: with `e = 3`, `f = 2`, `w = 2` and `y = 4` modulo `8`, `2 ^ 3 ≡ 4 ^ 2 ≡ 0`, but no
residue modulo `8` has cube `4`. -/
example : 2 ^ 3 ≡ 4 ^ 2 [MOD 8] ∧ ∀ x : ZMod 8, x ^ 3 ≠ 4 := ⟨by decide, by decide⟩

/-! ### Polynomial time -/

/-- `computableInPolyTime_commonRoot` on all five inputs `(n, e, f, w, y)`, read as nested pairs
on `encNat`. -/
example : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ × ℕ × ℕ => commonRoot p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat (encPair encNat encNat)))) encNat :=
  computableInPolyTime_commonRoot (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)

/-- `computableInPolyTime_commonRoot` for `n = 35`, `e = 3`, `f = 2`, `w = 4`, with `y` read from
`encNat`. -/
example : ComputableInPolyTime (fun y => commonRoot 35 3 2 4 y) encNat encNat :=
  computableInPolyTime_commonRoot (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop)

end CslibFrontierTests.Crypto.RSACommonRoot
