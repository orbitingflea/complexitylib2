/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Complexity.Classes.PCP.Robustness
import CslibFrontier.Computability.Complexity.Classes.PCP.ZeroRandomness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Tactic.NormNum

set_option linter.privateModule false

/-!
# Tests for PCP class robustness (`PCPWith_one`, `PCPWith_log_const`, `PCP_zero_log`)

Concrete verifiers exercising:
1. `PCPVerifier.repeatAll` and `PCPVerifier.acceptProb_repeatAll` on a verifier whose query count
   varies with the random string and repeats addresses across rounds (`Arora–Barak Ch. 18 §1`).
2. `PCPVerifier.tableAcceptCount`, `PCPVerifier.majorityTableVerifier`, `PCPWith_log_subset_NP`,
   and `PCPWith_log_const` (`Arora–Barak Ch. 18 §2`, corrected).
3. `PCPVerifier.exhaustiveTableDecider` and `PCP_zero_log`, including rejection when a zero-coin
   verifier makes contradictory queries to the same proof address (`Arora–Barak Ch. 18 §4(i)`).
-/

namespace CslibFrontierTests.PCPRobustness

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- A 1-coin verifier on `Bool`:
* on coin `[false]`, queries address `0` once and checks `a && π[0]`;
* on coin `[true]`, queries addresses `[0, 1]` and checks `π[0] && π[1]`.
For `a = false` and `π = [true, true]`, it accepts `[true]` and rejects `[false]`, giving
acceptance probability `1 / 2`. -/
private def halfSoundVerifier : PCPVerifier Bool where
  coins _ := 1
  queries p := if p.2.getD 0 false then [0, 1] else [0]
  verdict p :=
    if p.1.2.getD 0 false then
      p.2.getD 0 false && p.2.getD 1 false
    else
      p.1.1 && p.2.getD 0 false

private theorem halfSoundVerifier_polyTime : halfSoundVerifier.PolyTime encBool := by
  constructor <;> unfold halfSoundVerifier <;> fun_prop

-- Variable-length per-round query lists (`[0]` on round 0, `[0, 1]` on round 1) are resolved
-- consistently via first-occurrence lookup in `repeatQueries`.
example : halfSoundVerifier.repeatQueries 2 (false, [false, true]) = [0, 0, 1] := by decide

example : (halfSoundVerifier.repeatAll 2).accepts false [true, true] [false, true] = false := by
  decide

example : (halfSoundVerifier.repeatAll 2).accepts false [true, true] [true, true] = true := by
  decide

example : (halfSoundVerifier.repeatAll 2).accepts true [true, true] [false, true] = true := by
  decide

example : halfSoundVerifier.acceptCount false [true, true] = 1 := by decide

example : (halfSoundVerifier.repeatAll 3).acceptCount false [true, true] = 1 := by decide

example : (halfSoundVerifier.repeatAll 3).acceptProb false [true, true] = 1 / 8 := by
  rw [halfSoundVerifier.acceptProb_repeatAll 3 false [true, true], PCPVerifier.acceptProb]
  have hcnt : halfSoundVerifier.acceptCount false [true, true] = 1 := by decide
  rw [hcnt]
  simp [halfSoundVerifier]
  norm_num

example : (halfSoundVerifier.repeatAll 3).PolyTime encBool :=
  halfSoundVerifier.polyTime_repeatAll halfSoundVerifier_polyTime 3

-- Soundness amplification (`Arora–Barak Ch. 18 Problem 1`): any `0 < s < 1` gives `PCP`.
example (r q : ℕ → ℕ) : PCPWith 1 (99 / 100) r q encBool = PCP r q encBool :=
  PCPWith_one (by norm_num) (by norm_num) r q

example (r q : ℕ → ℕ) : PCPWith 1 (1 / 1000) r q encBool = PCP r q encBool :=
  PCPWith_one (by norm_num) (by norm_num) r q

-- Imperfect completeness (`Arora–Barak Ch. 18 Problem 2, corrected`):
-- majority table counting, concrete `IsPCPVerifierWith` with `c = 3 / 4 < 1` and `s = 1 / 2`,
-- `IsPCPVerifierWith.repeatAll`, `PCPWith_log_subset_NP`, and `PCPWith_log_const`.
example : halfSoundVerifier.tableAcceptCount (false, [true, true, true]) = 1 := by decide

example : halfSoundVerifier.majorityTableVerifier (false, [true, true, true]) = false := by decide

example : halfSoundVerifier.tableAcceptCount (true, [true, true, true]) = 2 := by decide

example : halfSoundVerifier.majorityTableVerifier (true, [true, true, true]) = true := by decide

/-- A 2-coin verifier on `Bool` for `{a : Bool | a = true}` with imperfect completeness `3 / 4` and
soundness `1 / 2`:
* when `a = true` and `π = [true]`, accepts the 3 random words `[false, false]`, `[false, true]`,
  `[true, false]` and rejects `[true, true]`;
* when `a = false`, ignores `π` and accepts `[false, false]` and `[false, true]`. -/
private def threeQuarterVerifier : PCPVerifier Bool where
  coins _ := 2
  queries _ := [0]
  verdict p :=
    if p.1.1 then
      !(p.1.2.getD 0 false && p.1.2.getD 1 false) && p.2.getD 0 false
    else
      !p.1.2.getD 0 false

private theorem threeQuarterVerifier_polyTime : threeQuarterVerifier.PolyTime encBool := by
  constructor <;> unfold threeQuarterVerifier <;> fun_prop

private theorem threeQuarterVerifier_isPCPVerifierWith :
    IsPCPVerifierWith encBool (3 / 4) (1 / 2)
      (fun n => 2 * (Nat.log 2 n + 1)) (fun _ => 1 * 1)
      threeQuarterVerifier {a : Bool | a = true} where
  coins_le a := by
    simp only [threeQuarterVerifier]
    omega
  length_queries_le a _ _ := by simp [threeQuarterVerifier]
  complete a ha := by
    subst ha
    refine ⟨[true], ?_⟩
    rw [PCPVerifier.acceptProb]
    have hcnt : threeQuarterVerifier.acceptCount true [true] = 3 := by decide
    rw [hcnt]
    simp [threeQuarterVerifier]
    norm_num
  sound a ha π := by
    have hfalse : a = false := Bool.eq_false_iff.mpr ha
    subst hfalse
    rw [PCPVerifier.acceptProb]
    have hcnt : threeQuarterVerifier.acceptCount false π = 2 :=
      show threeQuarterVerifier.acceptCount false [] = 2 by decide
    rw [hcnt]
    simp [threeQuarterVerifier]
    norm_num

example :
    IsPCPVerifierWith encBool ((3 / 4 : ℝ) ^ 2) ((1 / 2 : ℝ) ^ 2)
      (fun n => 2 * (2 * (Nat.log 2 n + 1))) (fun _ => 2 * (1 * 1))
      (threeQuarterVerifier.repeatAll 2) {a : Bool | a = true} :=
  threeQuarterVerifier_isPCPVerifierWith.repeatAll (by norm_num) 2

example (a : Bool) :
    a ∈ ({b : Bool | b = true} : Set Bool) ↔
      ∃ table, threeQuarterVerifier.majorityTableVerifier (a, table) = true :=
  threeQuarterVerifier_isPCPVerifierWith.mem_iff_exists_majorityTableVerifier (by norm_num) a

example : {a : Bool | a = true} ∈ NP encBool :=
  PCPWith_log_subset_NP (c := 3 / 4) (by norm_num) (fun _ => 1)
    ⟨threeQuarterVerifier, 2, 1, threeQuarterVerifier_polyTime,
      threeQuarterVerifier_isPCPVerifierWith⟩

example :
    PCPWith (3 / 4) (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => 3) encBool =
      PCP (fun n => Nat.log 2 n + 1) (fun _ => 3) encBool :=
  PCPWith_log_const (by norm_num) (by norm_num) (by decide)

/-- A zero-randomness verifier that queries the same proof address `[0, 0]` twice and demands
contradictory answers `ans[0] == false && ans[1] == true`. No genuine proof `π` can satisfy both
queries, and `exhaustiveTableDecider` rejects because `tableVerifier` enforces first-occurrence
consistency. -/
private def contradictoryZeroVerifier : PCPVerifier Bool where
  coins _ := 0
  queries _ := [0, 0]
  verdict p := !p.2.getD 0 false && p.2.getD 1 false

example : contradictoryZeroVerifier.exhaustiveTableDecider true = false := by decide

example : ∀ π : List Bool, contradictoryZeroVerifier.accepts true π [] = false := by
  intro π
  simp [PCPVerifier.accepts, PCPVerifier.answers, contradictoryZeroVerifier]

-- `PCP(0, log n) = P` (`Arora–Barak Ch. 18 Problem 4(i)`).
example : PCP (fun _ => 0) (fun n => Nat.log 2 n + 1) encBool = P encBool :=
  PCP_zero_log

end CslibFrontierTests.PCPRobustness
