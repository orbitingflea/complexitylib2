/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.RSAHash
import Mathlib.Tactic.NormNum.Prime

/-!
# Collision resistance from RSA: checked instances

Checks for `CslibFrontier/Crypto/Computational/RSAHash.lean`:

* For `N = 15`, `e = 3` and `y = 2`, the words of `(1, 0)` and `(2, 1)` are valid and collide:
  `1 ^ 3 * 2 ^ 0 = 1` and `2 ^ 3 * 2 ^ 1 = 16 ≡ 1 [MOD 15]`. From them `rsaHashRoot` returns `8`,
  and `8 ^ 3 ≡ 2 [MOD 15]`, as `rsaEval_rsaHashRoot` says.
* The canonical-encoding check matters: with a trailing `false`, the word of `(1, 0)` still
  decodes to `(1, 0)` but is not valid.
* `rsaEval_rsaHashRoot` needs `e` coprime to the distance of the exponents, not prime.
  `e = 9` is coprime to `(3 - 1) * (5 - 1) = 8`, so it belongs to an `RSADesc`, and `(1, 0)` and
  `(2, 3)` collide at `y = 2`. Their distance `3` is not coprime to `9`, and `rsaHashRoot` returns
  `1`, which is not a ninth root of `2`. At the same `e = 9`, `(4, 0)` and `(1, 2)` collide at
  `y = 2`, `9` is coprime to their distance `2`, and `rsaEval_rsaHashRoot` gives the ninth root.
* The certificates apply: `computableInPolyTime_rsaHash`, `computableInPolyTime_validRSAHashInput`,
  `computableInPolyTime_rsaHashRoot` on seven inputs read as nested pairs on `encNat`, and
  `isPPT_rsaHashToRSA` on the collision finder that always returns the same pair.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.RSAHash

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-- The key `N = 15 = 3 * 5`, `e = 3`, `d = 3`: `3 * 3 = 9 ≡ 1 [MOD 8]`. -/
def desc15 : RSADesc :=
  { p := 3, q := 5, e := 3, d := 3, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- The key `N = 15` with the exponent `e = 9`, which is coprime to `8` but not prime. -/
def desc15e9 : RSADesc :=
  { p := 3, q := 5, e := 9, d := 1, hp := by norm_num, hq := by norm_num, hpq := by decide,
    he := by decide, hed := by decide }

/-- The hash key `(15, 3, 2)`. -/
def key15 : RSAHashKey := ⟨desc15.publicKey, 2⟩

/-- The word of the pair `(1, 0)`. -/
def word₁ : List Bool := encPair encNat encNat (1, 0)

/-- The word of the pair `(2, 1)`. -/
def word₂ : List Bool := encPair encNat encNat (2, 1)

/-! ### A collision and its root -/

example : rsaHash key15 word₁ = 1 ∧ rsaHash key15 word₂ = 1 := by
  decide +kernel

example : validRSAHashInput 0 key15 word₁ = true ∧ validRSAHashInput 0 key15 word₂ = true := by
  decide +kernel

example : isCollisionFor (Param := RSAHashKey) (Digest := fun _ => ℕ) rsaHash validRSAHashInput
    0 key15 word₁ word₂ = true := by
  decide +kernel

/-- Shamir's trick with `f = 1 - 0 = 1` returns `w = 1 * 2⁻¹ = 8 (mod 15)`. -/
example : rsaHashRoot 15 3 2 1 0 2 1 = 8 := by
  unfold rsaHashRoot commonRoot BinaryGcd.modInv
  decide

example : rsaEval 15 3 8 = 2 := by decide

example : rsaEval 15 3 (rsaHashRoot 15 3 2 1 0 2 1) = 2 :=
  rsaEval_rsaHashRoot (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### The canonical-encoding check -/

example : rsaHashDecoder.decode (word₁ ++ [false]) = (1, 0) := by
  decide +kernel

example : validRSAHashInput 0 key15 (word₁ ++ [false]) = false := by
  decide +kernel

/-! ### `e` must be coprime to the distance, not prime -/

/-- `1 ^ 9 * 2 ^ 0 = 1` and `2 ^ 9 * 2 ^ 3 = 4096 ≡ 1 [MOD 15]`. -/
example : (1 ^ 9 * 2 ^ 0 : ℕ) ≡ 2 ^ 9 * 2 ^ 3 [MOD desc15e9.modulus] := by decide

/-- `9` is not coprime to the distance `3` of the exponents, so `rsaEval_rsaHashRoot` does not
apply. -/
example : ¬ Nat.Coprime 9 (Nat.dist 0 3) := by decide

example : rsaHashRoot 15 9 2 1 0 2 3 = 1 := by
  unfold rsaHashRoot commonRoot BinaryGcd.modInv
  decide

example : rsaEval 15 9 (rsaHashRoot 15 9 2 1 0 2 3) ≠ 2 := by
  unfold rsaHashRoot commonRoot BinaryGcd.modInv
  decide

/-- At the composite `e = 9`, `(4, 0)` and `(1, 2)` collide at `y = 2`:
`4 ^ 9 * 2 ^ 0 ≡ 4 ≡ 1 ^ 9 * 2 ^ 2 [MOD 15]`, and `9` is coprime to the distance `2`. -/
example : rsaEval 15 9 (rsaHashRoot 15 9 2 4 0 1 2) = 2 :=
  rsaEval_rsaHashRoot (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide)

/-! ### Certificates -/

example : ComputableInPolyTime (fun p : RSAHashKey × List Bool => rsaHash p.1 p.2)
    (encPair encRSAHashKey encBits) encNat :=
  computableInPolyTime_rsaHash

example : ComputableInPolyTime
    (fun p : (ℕ × RSAHashKey) × List Bool => validRSAHashInput p.1.1 p.1.2 p.2)
    (encPair (encPair encUnary encRSAHashKey) encBits) encBool :=
  computableInPolyTime_validRSAHashInput

example : ComputableInPolyTime
    (fun a : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ =>
      rsaHashRoot a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2.1 a.2.2.2.2.2.1 a.2.2.2.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat (encPair encNat (encPair encNat
      (encPair encNat encNat)))))) encNat :=
  computableInPolyTime_rsaHashRoot (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop)

/-- The collision finder that always returns the words of `(1, 0)` and `(2, 1)`. -/
noncomputable def constFinder : CollisionFinderFor RSAHashKey := fun _ _ => pure (word₁, word₂)

theorem isPPTOn_constFinder :
    IsPPTOn (encPair encUnary encRSAHashKey) (encPair encBits encBits)
      (fun p => constFinder p.1 p.2) :=
  (ComputableInPolyTime.const (word₁, word₂)).isPPTOn

example : (rsaHashToRSA constFinder).IsPPT := isPPT_rsaHashToRSA isPPTOn_constFinder

end CslibFrontierTests.Crypto.RSAHash
