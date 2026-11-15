/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.GUOAccumulator
import Mathlib.Tactic.NormNum.Prime

/-!
# The accumulator from a group of unknown order: checked instances

Checks for `CslibFrontier/Crypto/Computational/GUOAccumulator.lean`, modulo `N = 35` with base
`g = 2` and the elements `0`, `1`, `2` hashed to `3`, `5`, `7`:

* The commitment to `{0, 1}` is `2 ^ 15 ≡ 8`, with membership proofs `32` and `8`; inserting `2`
  gives `8 ^ 7 ≡ 22`. Alice's non-membership proof for `2` is `(b, γ) = (2, -6)`, and it verifies;
  her attempt for the member `0` does not.
* For the commitment `22` to all three elements, the membership proofs of `0` and `1` are `18` and
  `22`; Shamir's trick combines them into `23 = 2 ^ 7`, the aggregate proof, and `23 ^ 5 ≡ 18`
  splits it again.
* The hypotheses are needed: aggregation fails against a commitment that is not a unit, Alice's
  non-membership proof fails for a base that is not a unit and for a hash that divides `E`, and
  composite hashes can be distinct without being coprime. Without the unit check on `c`, the
  values `(c, a, b, γ) = (0, 0, 0, -1)` would pass both checks.
* `guoForgeryRoot` turns a membership and a non-membership proof for one element into a root of
  `g`, for `γ = 0` and for `γ < 0`.
* The polynomial-time certificates apply to inputs read from `encNat` and `encIntBin`, and Alice's
  coefficient is certified both as the natural number `-γ` and as the integer `γ`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.GUOAccumulator

open Cslib.Crypto Turing.MultiTapeTM

/-- The hash of the examples: `0 ↦ 3`, `1 ↦ 5`, and every other element to `7`. -/
def testH : ℕ → ℕ
  | 0 => 3
  | 1 => 5
  | _ => 7

/-! ### Commitment, membership proofs and the update -/

example : guoExponent testH {0, 1} = 15 := by decide

example : guoCommit 35 2 testH {0, 1} = 8 := by decide

/-- The membership proofs `π_0 = 2 ^ 5 = 32` and `π_1 = 2 ^ 3 = 8`. -/
example : guoSubsetWitness 35 2 testH {0, 1} {0} = 32 ∧
    guoSubsetWitness 35 2 testH {0, 1} {1} = 8 := by decide

example : guoVerifySubset 35 8 3 32 = true ∧ guoVerifySubset 35 8 5 8 = true := by decide

example : guoVerifySubset 35 (guoCommit 35 2 testH {0, 1}) (testH 0)
    (guoSubsetWitness 35 2 testH {0, 1} {0}) = true :=
  guoVerifySubset_singleton 35 2 testH (by decide)

/-- Inserting `2` raises the commitment to the power `7`: `8 ^ 7 ≡ 22`. -/
example : guoCommit 35 2 testH (insert 2 {0, 1}) = powMod 35 (guoCommit 35 2 testH {0, 1}) 7 :=
  guoCommit_insert 35 2 testH (by decide)

example : powMod 35 8 7 = 22 ∧ guoCommit 35 2 testH {0, 1, 2} = 22 := by decide

/-! ### Non-membership proofs -/

/-- Alice's proof for `2`: `-γ = 6`, the inverse of `-15 ≡ 6` modulo `7`, and
`β = (6 * 15 + 1) / 7 = 13`, so `b = 2 ^ 13 ≡ 2`. -/
example : guoNonMemCoeff 7 15 = 6 ∧ guoNonMemWitness 35 2 7 15 = 2 := by
  unfold guoNonMemWitness guoNonMemCoeff BinaryGcd.modInv
  decide

/-- Bob's check: `2 ^ 7 ≡ 23 ≡ 2 * 8 ^ 6`. -/
example : guoVerifyNonMem 35 2 8 7 2 (-6) = true := by decide

example : guoVerifyNonMem 35 2 (guoCommit 35 2 testH {0, 1}) (testH 2)
    (guoNonMemWitness 35 2 (testH 2) (guoExponent testH {0, 1}))
    (-(guoNonMemCoeff (testH 2) (guoExponent testH {0, 1}) : ℤ)) = true :=
  guoVerifyNonMem_guoCommit 35 2 (by decide) (by norm_num [testH])
    (by simp [testH]; norm_num) (by simp [testH])

example : guoNonMemCoeff 7 15 < 7 := guoNonMemCoeff_lt (by norm_num) 15

/-- Alice's attempt for the member `0`, whose hash `3` divides `E = 15`, does not verify. -/
example : guoVerifyNonMem 35 2 8 3 (guoNonMemWitness 35 2 3 15)
    (-(guoNonMemCoeff 3 15 : ℤ)) = false := by
  unfold guoNonMemWitness guoNonMemCoeff BinaryGcd.modInv
  decide

/-! ### Aggregation -/

/-- The membership proofs of `0` and `1` against the commitment `22` to `{0, 1, 2}`. -/
example : guoSubsetWitness 35 2 testH {0, 1, 2} {0} = 18 ∧
    guoSubsetWitness 35 2 testH {0, 1, 2} {1} = 22 := by decide

/-- Shamir's trick returns `23 = 2 ^ 7`, the aggregate proof of `{0, 1}`. -/
example : commonRoot 35 3 5 18 22 = 23 ∧ guoSubsetWitness 35 2 testH {0, 1, 2} {0, 1} = 23 := by
  unfold commonRoot BinaryGcd.modInv
  decide

example : guoVerifySubset 35 22 (3 * 5) (commonRoot 35 3 5 18 22) = true :=
  guoVerifySubset_commonRoot (by decide) (by decide) (by decide) (by decide)

example : guoVerifySubset 35 (guoCommit 35 2 testH {0, 1, 2}) (testH 0 * testH 1)
    (guoSubsetWitness 35 2 testH {0, 1, 2} {0, 1}) = true :=
  guoVerifySubset_pair 35 2 testH (by decide) (by decide) (by decide)

example : guoVerifySubset 35 (guoCommit 35 2 testH {0, 1, 2}) (guoExponent testH {0, 1})
    (guoSubsetWitness 35 2 testH {0, 1, 2} {0, 1}) = true :=
  guoVerifySubset_subsetWitness 35 2 testH (by decide)

/-- The aggregate splits: `23 ^ 5 ≡ 18`, the membership proof of `0`. -/
example : powMod 35 23 5 = 18 ∧ guoVerifySubset 35 22 3 (powMod 35 23 5) = true :=
  ⟨by decide, guoVerifySubset_split (f := 5) (by decide)⟩

/-! ### The hypotheses are needed -/

/-- Aggregation needs a unit commitment: modulo `6`, `2` passes Bob's check against `c = 2`, which
is not a unit, with the exponents `3` and `5`, but Shamir's trick returns `4`, which fails with
`15`. -/
example : guoVerifySubset 6 2 3 2 = true ∧ guoVerifySubset 6 2 5 2 = true ∧
    commonRoot 6 3 5 2 2 = 4 ∧ guoVerifySubset 6 2 15 (commonRoot 6 3 5 2 2) = false := by
  unfold commonRoot BinaryGcd.modInv
  decide

/-- Alice's non-membership proof needs a unit base: for `(N, g, h, E) = (15, 3, 5, 6)` the
commitment `3 ^ 6 ≡ 9` is not a unit. -/
example : guoVerifyNonMem 15 3 (powMod 15 3 6) 5 (guoNonMemWitness 15 3 5 6)
    (-(guoNonMemCoeff 5 6 : ℤ)) = false := by
  unfold guoNonMemWitness guoNonMemCoeff BinaryGcd.modInv
  decide

/-- It needs `0 < h`: for `(N, g, h, E) = (3, 2, 0, 1)` the proof fails. -/
example : guoVerifyNonMem 3 2 (powMod 3 2 1) 0 (guoNonMemWitness 3 2 0 1)
    (-(guoNonMemCoeff 0 1 : ℤ)) = false := by
  unfold guoNonMemWitness guoNonMemCoeff BinaryGcd.modInv
  decide

/-- It holds for `h = 1`, so the hypothesis is `0 < h`, not `1 < h`. -/
example : guoVerifyNonMem 35 2 (powMod 35 2 15) 1 (guoNonMemWitness 35 2 1 15)
    (-(guoNonMemCoeff 1 15 : ℤ)) = true :=
  guoVerifyNonMem_witness (by decide) (by norm_num) (by decide)

/-- Primality: the hashes `4` and `2` are distinct and not coprime, in either order. -/
example : ¬ Nat.Coprime 4 (guoExponent (fun _ : ℕ => 2) {0}) ∧
    ¬ Nat.Coprime 2 (guoExponent (fun _ : ℕ => 4) {0}) := by decide

/-- With a collision, `gcd(H x, E) ≠ 1` exhibits it. -/
example : ∃ y ∈ ({0} : Finset ℕ), y ≠ 1 ∧ (fun _ : ℕ => 3) y = (fun _ : ℕ => 3) 1 :=
  exists_collision_of_not_coprime_guoExponent (by norm_num) (by simp; norm_num) (by decide)
    (by decide)

example : Nat.Coprime (testH 2) (guoExponent testH {0, 1}) :=
  coprime_guoExponent (by norm_num [testH]) (by simp [testH]; norm_num) (by simp [testH])

/-- The unit check on `c` is needed: `(c, a, b, γ) = (0, 0, 0, -1)` passes the membership check
and the equation of the non-membership check modulo `35`, for the hash `3`, but `0` is not a unit,
so `guoVerifyNonMem` rejects it. -/
example : guoVerifySubset 35 0 3 0 = true ∧ (powMod 35 0 3 == 2 * powMod 35 0 1 % 35) = true ∧
    guoVerifyNonMem 35 2 0 3 0 (-1) = false := by decide

/-! ### The root from a membership and a non-membership proof -/

/-- Modulo `15` with `g = 2` and the hash `3`, `a = 2` is a membership proof against `c = 8`, and
`(b, γ) = (8, 0)` a non-membership proof, since `8 ^ 3 ≡ 2`. The root is `8`. -/
example : guoVerifySubset 15 8 3 2 = true ∧ guoVerifyNonMem 15 2 8 3 8 0 = true ∧
    guoForgeryRoot 15 2 8 0 = 8 := by decide

example : powMod 15 (guoForgeryRoot 15 2 8 0) 3 = 2 % 15 :=
  powMod_guoForgeryRoot (c := 8) (by decide) (by decide)

/-- With `γ = -1`: modulo `35` with `g = 32 = 2 ^ 5` and the hash `5`, `a = 3` proves membership
against `c = 3 ^ 5 ≡ 33`, and `(b, γ) = (6, -1)` non-membership, since `6 ^ 5 ≡ 6 ≡ 32 * 33`. The
root is `6 * 3⁻¹ ≡ 6 * 12 ≡ 2`. -/
example : guoVerifySubset 35 33 5 3 = true ∧ guoVerifyNonMem 35 32 33 5 6 (-1) = true ∧
    guoForgeryRoot 35 3 6 (-1) = 2 := by
  unfold guoForgeryRoot BinaryGcd.modInv
  decide

example : powMod 35 (guoForgeryRoot 35 3 6 (-1)) 5 = 32 % 35 :=
  powMod_guoForgeryRoot (c := 33) (by decide) (by decide)

/-! ### Polynomial time -/

/-- `computableInPolyTime_guoVerifySubset` on all four inputs, read as nested pairs on `encNat`. -/
example : ComputableInPolyTime (fun p : ℕ × ℕ × ℕ × ℕ => guoVerifySubset p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat encNat))) encBool :=
  computableInPolyTime_guoVerifySubset (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_guoVerifyNonMem` for `N = 35`, `g = 2`, `c = 8`, `h = 7`, with `b` read
from `encNat` and `γ` from `encIntBin`. -/
example : ComputableInPolyTime (fun p : ℕ × ℤ => guoVerifyNonMem 35 2 8 7 p.1 p.2)
    (encPair encNat encIntBin) encBool :=
  computableInPolyTime_guoVerifyNonMem (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_guoNonMemCoeff` on `(h, E)`, read as a pair on `encNat`: the natural
number `-γ`. -/
example : ComputableInPolyTime (fun p : ℕ × ℕ => guoNonMemCoeff p.1 p.2) (encPair encNat encNat)
    encNat :=
  computableInPolyTime_guoNonMemCoeff (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_neg_guoNonMemCoeff` for `h = 7`, with `E` read from `encNat`: Alice's `γ`
on `encIntBin`, the encoding in which `computableInPolyTime_guoVerifyNonMem` reads it. -/
example : ComputableInPolyTime (fun E : ℕ => -(guoNonMemCoeff 7 E : ℤ)) encNat encIntBin :=
  computableInPolyTime_neg_guoNonMemCoeff (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_guoNonMemWitness` on `(N, g, h, E)`, read as nested pairs on `encNat`. -/
example : ComputableInPolyTime
    (fun p : ℕ × ℕ × ℕ × ℕ => guoNonMemWitness p.1 p.2.1 p.2.2.1 p.2.2.2)
    (encPair encNat (encPair encNat (encPair encNat encNat))) encNat :=
  computableInPolyTime_guoNonMemWitness (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

/-- `computableInPolyTime_guoForgeryRoot` for `N = 35`, with `a`, `b` read from `encNat` and `γ`
from `encIntBin`. -/
example : ComputableInPolyTime (fun p : ℕ × ℕ × ℤ => guoForgeryRoot 35 p.1 p.2.1 p.2.2)
    (encPair encNat (encPair encNat encIntBin)) encNat :=
  computableInPolyTime_guoForgeryRoot (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)

end CslibFrontierTests.Crypto.GUOAccumulator
