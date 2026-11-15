/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.StrongRSA
import Mathlib.FieldTheory.Finite.Basic

/-!
# The strong RSA assumption: checked instances

Checks for `CslibFrontier/Crypto/Computational/StrongRSA.lean`:

* For `N = 15` and `g = 2`, `(8, 3)` is a solution: `8 ^ 3 = 512 ≡ 2 [MOD 15]`. The exponent `1`
  never wins: `(2, 1)` is not a solution although `2 ^ 1 = 2`.
* The known-order root: `2 ^ 4 ≡ 1 [MOD 15]` and `3` is coprime to `4`, and
  `knownOrderRoot 15 4 3 2 = 8`, the solution above, as `powMod_knownOrderRoot` says.
* `0 < u` is needed in `powMod_knownOrderRoot`: `2 ^ 0 ≡ 1 [MOD 5]` and `1` is coprime to `0`, but
  `knownOrderRoot 5 0 1 2 = 1`, and `1 ^ 1` is not `2` modulo `5`.
* `strongRSAGame_orderMultipleAdversary`: the order of `2` modulo `15` is `4`, so
  `orderMultipleAdversary` with `u = 4` wins with probability `1` against the constant setup
  `(15, 2)`.
* `not_strongRSA_rsaGUOSetup_const`: the book's `GGen` with a fixed RSA key does not satisfy the
  assumption. Every drawn base is a unit (`exists_of_mem_support_rsaGUOSetup`), so
  `not_strongRSA_of_orderMultiple` applies with the constant multiple `u = φ(N)` of the order.
* The unit condition in `not_strongRSA_const` (`AssumptionNonvacuity.lean`) is needed:
  for `(N, g) = (4, 2)` no output is a solution (`isStrongRSASolution_four_two`), so the strong
  RSA assumption holds for that constant setup (`strongRSA_const_four_two`). The same setup shows
  that `0 < u` is needed in `not_strongRSA_of_orderMultiple`: `u = 0` meets `2 ^ 0 ≡ 1 [MOD 4]`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.StrongRSA

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM

/-! ### A solution and the known-order root -/

example : isStrongRSASolution ⟨15, 2⟩ (8, 3) = true := by decide

example : isStrongRSASolution ⟨15, 2⟩ (2, 1) = false := by decide

example : knownOrderRoot 15 4 3 2 = 8 := by
  unfold knownOrderRoot BinaryGcd.modInv
  decide

example : powMod 15 (knownOrderRoot 15 4 3 2) 3 = 2 :=
  powMod_knownOrderRoot (by norm_num) (by decide) (by decide)

/-! ### `0 < u` is needed -/

example : 2 ^ 0 ≡ 1 [MOD 5] ∧ Nat.Coprime 1 0 ∧ knownOrderRoot 5 0 1 2 = 1 ∧
    powMod 5 (knownOrderRoot 5 0 1 2) 1 ≠ 2 % 5 := by
  refine ⟨rfl, by decide, ?_, ?_⟩ <;>
  · unfold knownOrderRoot BinaryGcd.modInv
    decide

/-! ### The order-multiple adversary -/

/-- The order of `2` modulo `15` is `4`, so `orderMultipleAdversary` with `u = 4` wins with
probability `1` against the constant setup `(N, g) = (15, 2)`. -/
example (n : ℕ) :
    strongRSAGame (fun _ => PMF.pure ⟨15, 2⟩) (orderMultipleAdversary fun _ _ => 4) n =
      PMF.pure true :=
  strongRSAGame_orderMultipleAdversary _ _ n fun p hp => by
    obtain rfl := (PMF.mem_support_pure_iff _ _).mp hp
    exact ⟨by norm_num, by decide⟩

/-! ### The book's `GGen` with a fixed key -/

/-- **`rsaGUOSetup` with a fixed RSA key does not satisfy the strong RSA assumption**: every base it
draws is a unit modulo `N`, so `g ^ φ(N) ≡ 1 [MOD N]`, and the order-multiple adversary with
`u = φ(N)` wins with probability `1`. -/
theorem not_strongRSA_rsaGUOSetup_const (desc : RSADesc) :
    ¬ StrongRSA (rsaGUOSetup fun _ => PMF.pure desc) := by
  refine not_strongRSA_of_orderMultiple (u := fun _ _ => desc.modulus.totient)
    (ComputableInPolyTime.const _) fun n p hp => ?_
  obtain ⟨d, hd, hN, hg⟩ := exists_of_mem_support_rsaGUOSetup hp
  obtain rfl : d = desc := by simpa using hd
  rw [hN] at hg ⊢
  exact ⟨Nat.totient_pos.mpr (Nat.pos_of_neZero _), Nat.ModEq.pow_totient hg⟩

/-! ### A base that is not a unit -/

/-- Modulo `4`, no `x ^ e` with `e ≠ 1` is `2`: for `e = 0` it is `1`, and for `e ≥ 2` an even
`x ^ e` is divisible by `4`. -/
theorem isStrongRSASolution_four_two (s : ℕ × ℕ) : isStrongRSASolution ⟨4, 2⟩ s = false := by
  obtain ⟨x, _ | _ | e⟩ := s
  · simp [isStrongRSASolution, powMod]
  · simp [isStrongRSASolution]
  · have h4 : ¬ x ^ (e + 2) % 4 = 2 := by
      intro h
      have hx : Even x :=
        (Nat.even_pow.mp (Nat.even_iff.mpr (show x ^ (e + 2) % 2 = 0 by omega))).1
      obtain ⟨k, rfl⟩ := hx
      have : 4 ∣ (k + k) ^ (e + 2) := Dvd.intro (k ^ 2 * (k + k) ^ e) (by ring)
      omega
    simp [isStrongRSASolution, powMod, h4]

/-- **The unit condition in `not_strongRSA_const` is needed**: the strong RSA assumption holds for
the constant setup `(N, g) = (4, 2)`, since no output wins (`isStrongRSASolution_four_two`). -/
theorem strongRSA_const_four_two : StrongRSA fun _ => PMF.pure ⟨4, 2⟩ := by
  intro A _
  have hfalse : isStrongRSASolution ⟨4, 2⟩ = fun _ => false := funext isStrongRSASolution_four_two
  have hgame (n : ℕ) : strongRSAGame (fun _ => PMF.pure ⟨4, 2⟩) A n = PMF.pure false := by
    simp only [strongRSAGame, Game.withSetup, PMF.pure_bind, ProbComp.eval_bind,
      ProbComp.eval_pure, hfalse]
    exact PMF.bind_const _ _
  simp [hgame, Game.succProbability]

/-- **`0 < u` is needed in `not_strongRSA_of_orderMultiple`**: `u = 0` meets `g ^ u ≡ 1 [MOD N]`
for every `(N, g)`, yet the strong RSA assumption holds for the constant setup `(4, 2)`. -/
example : (∀ p : GUOParams, p.base ^ 0 ≡ 1 [MOD p.modulus]) ∧
    StrongRSA fun _ => PMF.pure ⟨4, 2⟩ :=
  ⟨fun p => by rw [pow_zero], strongRSA_const_four_two⟩

end CslibFrontierTests.Crypto.StrongRSA
