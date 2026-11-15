/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.MerkleDamgard.Multicollision
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds

/-!
# Tests for Joux multicollisions

Checks for `CslibFrontier/Crypto/Computational/MerkleDamgard/Multicollision.lean` as a `module`
client with ordinary imports:

* Collision chains on numbers: a chain for `step t m = t + m % 2` and its four messages, which
  reach one value and are distinct; a list that is not a chain for `step t m = t * m`.
* Hypotheses that cannot be dropped: a pair of equal messages gives one message, not two; a step
  that is injective in the message has no collision chain.
* A collision chain gives a collision of the collision-resistance game, for any step on bits and
  for `merkleDamgard` with a compression function that ignores its block.
* The success events of the Merkle–Damgård theorems, opened through `mem_multicollisionOutputs`
  and `mem_bitMulticollisionOutputs`: `b` pairs whose selections are a multicollision, after every
  common suffix for chains; for `b = 1`, a collision of the collision-resistance game.
* Certificates on numbers: `merkleDamgardJouxFinder 8 5 9 3 [false]` makes at most 45 calls and
  `merkleDamgardBitJouxFinder 1 8 5 9 3` at most 361; with no budget the finder is `pure none`.
* The success bounds are not vacuous: for every compression function with one-bit chaining values
  and eight-bit blocks, 45 calls give an 8-collision with probability at least `3/4`, and the same
  holds for the generic finder with any step on `Bool`. The headline theorems at the book's
  parameters (`n = 1`, `ℓ = g = 8`, `b = 3`, budget 9) give at least `1/2`.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.MerkleDamgardMulticollision

open Cslib Cslib.Crypto

/-! ## Collision chains -/

/-- A chain for `step t m = t + m % 2` on `ℕ`, and its four messages. -/
example : IsCollisionChain (fun t m : ℕ => t + m % 2) 0 [(0, 2), (1, 3)] := by
  simp [IsCollisionChain]

example : jouxMessage [((0 : ℕ), 2), (1, 3)] ![true, false] = [2, 1] := by decide

/-- Every selection from the chain reaches the value `1` that the first messages reach. -/
example (σ : BitString 2) :
    (jouxMessage [((0 : ℕ), 2), (1, 3)] σ).foldl (fun t m : ℕ => t + m % 2) 0 = 1 := by
  have hc : IsCollisionChain (fun t m : ℕ => t + m % 2) 0 [(0, 2), (1, 3)] := by
    simp [IsCollisionChain]
  exact (hc.foldl_jouxMessage σ).trans rfl

/-- The four selections are different messages. -/
example : Function.Injective (jouxMessage [((0 : ℕ), 2), (1, 3)]) :=
  IsCollisionChain.jouxMessage_injective (step := fun t m : ℕ => t + m % 2) (t := 0)
    (by simp [IsCollisionChain])

/-- The four selections, each followed by `5`, are a 4-collision. -/
example : IsMulticollision (fun ms : List ℕ => (ms ++ [5]).foldl (fun t m => t + m % 2) 0) 4
    (Finset.univ.image (jouxMessage [((0 : ℕ), 2), (1, 3)])) :=
  IsCollisionChain.isMulticollision (by simp [IsCollisionChain]) [5]

/-- The second pair collides at `1`, the value reached through the first pair, but the pairs in
the other order are not a chain from `0` for `step t m = t * m`. -/
example : ¬ IsCollisionChain (fun t m : ℕ => t * m) 1 [(2, 3)] := by
  simp [IsCollisionChain]

/-- Without `p.1 ≠ p.2` the count fails: a pair of equal messages gives one message, not two. -/
example : (Finset.univ.image (jouxMessage [((0 : ℕ), 0)])).card = 1 := by decide

/-- A step that is injective in the message has no collision chain: the block-length condition of
the success theorems cannot be dropped. -/
example (t : ℕ) (p : ℕ × ℕ) : ¬ IsCollisionChain (fun _ m : ℕ => m) t [p] := by
  simp only [IsCollisionChain, and_true, not_and]
  exact fun hne h => hne h.symm

/-! ## From a chain to a collision of the collision-resistance game -/

/-- For any step on bits, one link of a collision chain gives a collision of the iterated function
in the sense of the collision-resistance game. -/
example (step : List Bool → Bool → List Bool) (t : List Bool) (p : Bool × Bool)
    (hc : IsCollisionChain step t [p]) :
    isCollision (fun _ ms => (ms ++ []).foldl step t) (fun _ _ => true) 0 [] [p.1] [p.2] =
      true := by
  refine isCollision_of_isMulticollision (hc.isMulticollision []) ?_ ?_ ?_ rfl rfl
  · exact Finset.mem_image.mpr ⟨![false], Finset.mem_univ _, by simp [jouxMessage]⟩
  · exact Finset.mem_image.mpr ⟨![true], Finset.mem_univ _, by simp [jouxMessage]⟩
  · simpa using hc.fst_ne_snd p (by simp)

/-- A compression function that keeps the chaining value and ignores the block: two different
one-bit groups collide from the value after the marker block, so `merkleDamgard` has a
2-collision, which is a collision of the collision-resistance game. -/
example : isCollision (merkleDamgard fun _ x => x.take 1) (fun _ _ => true) 0 [false] [false]
    [true] = true := by
  have hc : IsCollisionChain
      (fun t (m : BitString 1) => merkleDamgardChain (fun _ x => x.take 1) [false] t
        ((List.ofFn m).map (mdDataBlock [false].length)))
      ((fun _ x => x.take 1) [false] (List.replicate [false].length false ++
        mdEndBlock [false].length)) [(![false], ![true])] :=
    ⟨by decide, by decide, trivial⟩
  refine isCollision_of_isMulticollision (isMulticollision_merkleDamgard_of_chain hc) ?_ ?_
    (by decide) rfl rfl
  · exact Finset.mem_image.mpr ⟨![false], Finset.mem_univ _, by decide⟩
  · exact Finset.mem_image.mpr ⟨![true], Finset.mem_univ _, by decide⟩

/-- The same compression function on a chain with one-bit blocks: two one-block messages with one
chaining value. -/
example : IsMulticollision (fun bs => merkleDamgardChain (fun _ x => x.take 1) [false] [false]
      (bs ++ [])) 2
    ((Finset.univ.image (jouxMessage [((![false] : BitString 1), (![true] : BitString 1))])).image
      (List.map List.ofFn)) :=
  isMulticollision_merkleDamgardChain (h := fun _ x => x.take 1) (k := [false]) (iv := [false])
    (pairs := [(![false], ![true])]) ⟨by decide, by decide, trivial⟩ []

/-! ## Opening the success events -/

/-- An output in the success event of `merkleDamgardJouxFinder` is `b` pairs whose `2 ^ b`
selections, each followed by any common list of blocks, are a `2 ^ b`-collision of the chain. -/
example (h : List Bool → List Bool → List Bool) (k iv : List Bool) (ℓ b : ℕ)
    (pairs : List (BitString ℓ × BitString ℓ))
    (ho : some pairs ∈ multicollisionOutputs h k ℓ b iv) (tail : List (List Bool)) :
    pairs.length = b ∧
      IsMulticollision (fun bs => merkleDamgardChain h k iv (bs ++ tail)) (2 ^ b)
        ((Finset.univ.image (jouxMessage pairs)).image (List.map List.ofFn)) := by
  obtain ⟨p, hp, hlen, hm⟩ := mem_multicollisionOutputs.mp ho
  obtain rfl := Option.some.inj hp
  exact ⟨hlen, hm tail⟩

/-- The event does not hold for `none`, the output when the budget runs out. -/
example (h : List Bool → List Bool → List Bool) (k iv : List Bool) (ℓ b : ℕ) :
    none ∉ multicollisionOutputs h k ℓ b iv := by
  intro hn
  obtain ⟨_, hn, -⟩ := mem_multicollisionOutputs.mp hn
  cases hn

/-- An output in the success event of `merkleDamgardBitJouxFinder` with `b = 1` gives a collision
of `merkleDamgard h k` in the sense of the collision-resistance game. -/
example (h : List Bool → List Bool → List Bool) (k : List Bool) (g : ℕ)
    (pairs : List (BitString g × BitString g))
    (ho : some pairs ∈ bitMulticollisionOutputs h k g 1) :
    ∃ m₁ m₂, isCollision (merkleDamgard h) (fun _ _ => true) 0 k m₁ m₂ = true := by
  obtain ⟨p, hp, -, hm⟩ := mem_bitMulticollisionOutputs.mp ho
  obtain rfl := Option.some.inj hp
  obtain ⟨m₁, h₁, m₂, h₂, hne⟩ := Finset.one_lt_card.mp (lt_of_lt_of_eq (by norm_num) hm.1.symm)
  exact ⟨m₁, m₂, isCollision_of_isMulticollision hm h₁ h₂ hne rfl rfl⟩

/-- The event fixes the number of pairs: `b` pairs, not more. -/
example (h : List Bool → List Bool → List Bool) (k : List Bool) (g b : ℕ)
    (pairs : List (BitString g × BitString g))
    (ho : some pairs ∈ bitMulticollisionOutputs h k g b) : pairs.length = b := by
  obtain ⟨p, hp, hlen, -⟩ := mem_bitMulticollisionOutputs.mp ho
  obtain rfl := Option.some.inj hp
  exact hlen

/-! ## Absorbing message bits -/

/-- Absorbing two bits continues the chain over their two data blocks. -/
example (h : List Bool → List Bool → List Bool) (k t : List Bool) :
    (absorbBits 1 t [true, false]).run (fun x => pure (h k x)) =
      pure (merkleDamgardChain h k t [mdDataBlock 1 true, mdDataBlock 1 false]) :=
  run_absorbBits 1 t [true, false]

/-- Absorbing two bits costs at most two compression calls. -/
example (t : List Bool) : ProbOracleComp.IsQueryBounded (absorbBits 1 t [true, false]) 2 :=
  isQueryBounded_absorbBits 1 t _

/-! ## Certificates -/

/-- The certificate, on numbers: nine attempts of five blocks cost at most 45 calls. -/
example : ProbOracleComp.IsQueryBounded (merkleDamgardJouxFinder 8 5 9 3 [false]) 45 :=
  isQueryBounded_merkleDamgardJouxFinder 8 5 9 3 [false]

/-- Without a budget there is no output: the budget is what the certificate counts. -/
example : merkleDamgardJouxFinder 8 5 0 1 [false] = pure none := rfl

/-- The certificate for the library's function, on numbers: one call for the marker block and
nine attempts of five 8-bit groups. -/
example : ProbOracleComp.IsQueryBounded (merkleDamgardBitJouxFinder 1 8 5 9 3) 361 :=
  isQueryBounded_merkleDamgardBitJouxFinder 1 8 5 9 3

/-- The generic finder that asks its oracle for each step: nine attempts of five steps cost at
most 45 calls. -/
example (t : Bool) :
    ProbOracleComp.IsQueryBounded
      (jouxFinder (spec := fun _ : Bool × BitString 8 => Bool)
        (fun t m => ProbOracleComp.query (t, m)) (ProbComp.uniform (BitString 8)) 5 9 3 t) 45 :=
  isQueryBounded_jouxFinder (c := 1)
    (stage := fun (t : Bool) (m : BitString 8) =>
      ProbOracleComp.query (spec := fun _ : Bool × BitString 8 => Bool) (t, m))
    (fun t m => ProbOracleComp.IsQueryBounded.query (t, m)) (ProbComp.uniform (BitString 8)) 5 9 3 t

/-! ## Success probabilities -/

/-- One attempt with `N = 2`, `K = 256`, `s = 5` fails with probability at most `9/128`, in the
form of `merkleDamgardJouxFinder_success`. -/
private theorem test_attempt_failure_le :
    Real.exp (-(((5 : ℕ) : ℝ) * (((5 : ℕ) : ℝ) - 1) / (2 * 2 ^ 1))) +
      (Nat.choose 5 2 : ℕ) * ((2 : ℝ) ^ 8)⁻¹ ≤ 9 / 128 := by
  have he : Real.exp (-(((5 : ℕ) : ℝ) * (((5 : ℕ) : ℝ) - 1) / (2 * 2 ^ 1))) ≤ 1 / 32 :=
    (Real.exp_le_half_pow 5 (by norm_num)).trans_eq (by norm_num)
  have hc : ((Nat.choose 5 2 : ℕ) : ℝ) * ((2 : ℝ) ^ 8)⁻¹ = 10 / 256 := by
    norm_num [Nat.choose]
  rw [hc]
  linarith

/-- The same bound in the form of `jouxFinder_success` with `D = Finset.univ : Finset Bool` and
bytes as messages. -/
private theorem test_attempt_failure_le_univ :
    Real.exp (-(((5 : ℕ) : ℝ) * (((5 : ℕ) : ℝ) - 1) /
        (2 * ((Finset.univ : Finset Bool).card : ℝ)))) +
      ((Nat.choose 5 2 : ℕ) : ℝ) * ((Fintype.card (BitString 8) : ℕ) : ℝ)⁻¹ ≤ 9 / 128 := by
  rw [Finset.card_univ, Fintype.card_bool, BitString.card]
  exact_mod_cast test_attempt_failure_le

/-- The numbers of the non-vacuity examples: three stages, nine attempts. -/
private theorem three_quarters_le_test_bound :
    (3 / 4 : ℝ) ≤ 1 - 2 ^ 3 * ((1 + 9 / 128) / 2) ^ 9 / 2 := by
  norm_num

/-- The generic finder is not vacuous: for every step `Bool → BitString 8 → Bool`, asked of the
oracle, 45 calls give a collision chain of length three with probability at least `3/4`. -/
example (step : Bool → BitString 8 → Bool) :
    (3 / 4 : ℝ) ≤
      ((ProbComp.eval ((jouxFinder (spec := fun _ : Bool × BitString 8 => Bool)
        (fun t m => ProbOracleComp.query (t, m)) (ProbComp.uniform (BitString 8)) 5 9 3
          false).run fun x => pure (step x.1 x.2))).toOuterMeasure
            (jouxSuccess step 3 false)).toReal :=
  three_quarters_le_test_bound.trans
    (jouxFinder_success (spec := fun _ : Bool × BitString 8 => Bool)
      (stage := fun t m => ProbOracleComp.query (t, m)) (fun x => step x.1 x.2) step
      (fun t m => ProbOracleComp.run_query (t, m) _) Finset.univ (fun _ _ _ => Finset.mem_univ _)
      5 test_attempt_failure_le_univ 9 3 (Finset.mem_univ _))

/-- The bound is not vacuous: for every compression function with one-bit chaining values and
eight-bit blocks, 45 evaluations give an 8-collision with probability at least `3/4`. -/
example (h : List Bool → List Bool → List Bool) (k : List Bool)
    (hlen : ∀ x, x.length = 1 + 8 → (h k x).length = 1) :
    (3 / 4 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardJouxFinder 8 5 9 3 [false]).run
        fun x => pure (h k x))).toOuterMeasure
          (multicollisionOutputs h k 8 3 [false])).toReal :=
  three_quarters_le_test_bound.trans
    (merkleDamgardJouxFinder_success hlen rfl 5 test_attempt_failure_le 9 3)

/-- The book's parameters on the same sizes: eight-bit blocks are seven bits longer than one-bit
chaining values. -/
example (h : List Bool → List Bool → List Bool) (k : List Bool)
    (hlen : ∀ x, x.length = 1 + 8 → (h k x).length = 1) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardJouxFinder 8 (⌈2 * Real.sqrt ((2 ^ 1 : ℕ) : ℝ)⌉₊ + 1)
        (3 * 3) 3 [false]).run fun x => pure (h k x))).toOuterMeasure
          (multicollisionOutputs h k 8 3 [false])).toReal :=
  merkleDamgardJouxFinder_success_half hlen rfl (by norm_num) 3

/-- The same for the library's `merkleDamgard` with a one-bit key: 361 evaluations give eight
24-bit messages with one digest, with probability at least `3/4`, whatever `h` is. -/
example (h : List Bool → List Bool → List Bool)
    (hlen : ∀ x, x.length = 2 * [false].length → (h [false] x).length = [false].length) :
    (3 / 4 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardBitJouxFinder 1 8 5 9 3).run
        fun x => pure (h [false] x))).toOuterMeasure
          (bitMulticollisionOutputs h [false] 8 3)).toReal :=
  three_quarters_le_test_bound.trans
    (merkleDamgardBitJouxFinder_success hlen 8 5 test_attempt_failure_le 9 3)

/-- The book's sample count for the library's `merkleDamgard`, with eight-bit groups. -/
example (h : List Bool → List Bool → List Bool)
    (hlen : ∀ x, x.length = 2 * [false].length → (h [false] x).length = [false].length) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((merkleDamgardBitJouxFinder [false].length 8
        (⌈2 * Real.sqrt ((2 ^ [false].length : ℕ) : ℝ)⌉₊ + 1) (3 * 3) 3).run
          fun x => pure (h [false] x))).toOuterMeasure
            (bitMulticollisionOutputs h [false] 8 3)).toReal :=
  merkleDamgardBitJouxFinder_success_half hlen (by simp) 3

end CslibFrontierTests.MerkleDamgardMulticollision
