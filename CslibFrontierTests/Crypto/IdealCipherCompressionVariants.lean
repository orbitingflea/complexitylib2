/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test suite)

public import CslibFrontier.Crypto.Primitives.IdealCipher.CompressionVariants
import CslibFrontier.Languages.Probabilistic.Notation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for Insecure Block-Cipher Compression Variants

Concrete checks on `BitString`, `ZMod 5`, and `ZMod 16`, a subsingleton impossibility example,
and a choice-free axiom guard for `keyMaskedInput_collision`.
-/

public section

open Cslib Cslib.Crypto.BlockCipherCompression Cslib.IdealCipher Cslib.OracleComp Cslib.Probability

namespace IdealCipherCompressionVariantsTests

/-- Explicit 2-query collision finder for `keyMasked` (`h₄` with arguments swapped) on `n`-bit
strings. -/
def bitStringH4Adversary (n : ℕ) : CollisionFinder (BitString n) (BitString n) :=
  keyMaskedAdversary (fun _ => false) (fun _ => true) (fun _ => false)

/-- Explicit 2-query collision finder for `keyMaskedInput` (`h₅`) on `n`-bit strings. -/
def bitStringH5Adversary (n : ℕ) : CollisionFinder (BitString n) (BitString n) :=
  keyMaskedInputAdversary (fun _ => false) (fun _ => true) (fun _ => false)

theorem bitStringH4Adversary_wins {n : ℕ} (hn : 1 ≤ n) :
    Pr[collisionGame (keyMasked (B := BitString n)) (bitStringH4Adversary n)] = 1 := by
  have hk : (fun _ : Fin n => false) ≠ (fun _ : Fin n => true) := by
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  rw [bitStringH4Adversary, keyMaskedAdversary_wins hk]
  simp

theorem bitStringH5Adversary_wins {n : ℕ} (hn : 1 ≤ n) :
    Pr[collisionGame (keyMaskedInput (B := BitString n)) (bitStringH5Adversary n)] = 1 := by
  have hk : (fun _ : Fin n => false) ≠ (fun _ : Fin n => true) := by
    intro h
    have := congrFun h ⟨0, hn⟩
    simp at this
  rw [bitStringH5Adversary, keyMaskedInputAdversary_wins hk]
  simp

example :
    collisionGame (keyMasked (B := ZMod 16)) (keyMaskedAdversary (0 : ZMod 16) 1 0) =
      PMF.pure true :=
  keyMaskedAdversary_wins (by decide) 0

example :
    collisionGame (keyMaskedInput (B := ZMod 16))
        (keyMaskedInputAdversary (0 : ZMod 16) 1 0) = PMF.pure true :=
  keyMaskedInputAdversary_wins (by decide) 0

instance : Fact (1 < 16) := ⟨by norm_num⟩

example : ∃ A : CollisionFinder (ZMod 16) (ZMod 16),
    IsQueryBounded A 2 ∧ Pr[collisionGame (keyMasked (B := ZMod 16)) A] = 1 :=
  exists_collisionFinder_keyMasked

example : ∃ A : CollisionFinder (ZMod 16) (ZMod 16),
    IsQueryBounded A 2 ∧ Pr[collisionGame (keyMaskedInput (B := ZMod 16)) A] = 1 :=
  exists_collisionFinder_keyMaskedInput

example : ¬ ∃ A : CollisionFinder (ZMod 16) (ZMod 16),
    IsQueryBounded A 2 ∧
      Pr[collisionGame (daviesMeyer (K := ZMod 16) (B := ZMod 16)) A] = 1 := by
  rintro ⟨A, hA, h1⟩
  have h := daviesMeyer_collisionGame_mul_le hA
  have hcard : Fintype.card (ZMod 16) = 16 := ZMod.card 16
  rw [hcard, h1] at h
  norm_num at h

private def xorCipher2 (k : BitString 2) : Equiv.Perm (BitString 2) :=
  Equiv.addLeft k

example :
    (![false, false], -![false, false] + (xorCipher2 ![false, false]).symm (0 - ![false, false])) ≠
      (![true, true], -![true, true] + (xorCipher2 ![true, true]).symm (0 - ![true, true])) :=
  (keyMaskedInput_collision xorCipher2 (k := ![false, false]) (k' := ![true, true])
    (by decide) 0).1

example :
    keyMaskedInput xorCipher2 (![false, false], ![false, false]) =
      keyMaskedInput xorCipher2 (![true, true], ![true, true]) := by
  decide

private def swapCipher (k : ZMod 5) : Equiv.Perm (ZMod 5) :=
  Equiv.swap k (k + 1)

example : ∀ k y : ZMod 5,
    keyMaskedInput swapCipher (k, -k + (swapCipher k).symm (y - k)) = y := by
  decide

example : keyMaskedInput swapCipher (1, 1) = 2 ∧ keyMaskedInput swapCipher (3, 0) = 2 := by
  decide

private theorem collisionGame_eq_pure_false_of_subsingleton {Key Block : Type} [DecidableEq Key]
    [Fintype Key] [DecidableEq Block] [Fintype Block] [Nonempty Block] [Subsingleton Key]
    [Subsingleton Block]
    (H : (Key → Equiv.Perm Block) → Key × Block → Block) (A : CollisionFinder Key Block) :
    collisionGame H A = PMF.pure false := by
  unfold collisionGame
  have hcol : ∀ (E : Key → Equiv.Perm Block) (x₁ x₂ : Key × Block),
      collides x₁ x₂ (H E x₁) (H E x₂) = false := by
    intro E x₁ x₂
    simp [collides, Subsingleton.elim x₁ x₂]
  have hmap : ∀ E : Key → Equiv.Perm Block,
      ((OracleComp.interpret lazyEvalPerm A E).map fun ((x₁, x₂), _) =>
        collides x₁ x₂ (H E x₁) (H E x₂)) = PMF.pure false := by
    intro E
    simp_rw [hcol]
    exact PMF.map_const _ false
  simp_rw [hmap]
  exact PMF.bind_const _ (PMF.pure false)

example (A : CollisionFinder Unit Unit) :
    Pr[collisionGame (keyMasked (B := Unit)) A] = 0 := by
  rw [collisionGame_eq_pure_false_of_subsingleton]
  simp

/-- info: 'Cslib.Crypto.BlockCipherCompression.keyMaskedInput_collision' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Crypto.BlockCipherCompression.keyMaskedInput_collision

end IdealCipherCompressionVariantsTests
