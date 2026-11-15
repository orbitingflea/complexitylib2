/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.IdealCipher.Compression
import CslibFrontier.Languages.Probabilistic.Notation

/-!
# Explicit Collisions for Insecure Block-Cipher Compression Variants

Building on `Cslib.IdealCipher` (`CslibFrontier.Crypto.Primitives.IdealCipher.Compression`), this
module records explicit 2-query ideal-cipher collision finders for two insecure variants of
Davies–Meyer from [BonehShoup2023], Section 8.5.2 (p. 301) and Exercise 8.11 (p. 349):

* `keyMasked`, defined by `h(k, x) = F_k(x) + k` ([KatzLindell2020], Exercise 7.23(c)), which is
  `h₄` with its two arguments swapped;
* `keyMaskedInput`, defined by `h₅(k, x) = F_k(k + x) + k`.

Both variants are modeled purely in the ideal-cipher model (`CollisionFinder` and `collisionGame`
over an arbitrary finite additive group `Block`); no computational `BlockCipher` or
`CollisionResistantForOn` corollary is formalized here.

## Main definitions

* `Cslib.IdealCipher.keyMaskedAdversary`: 2-query ideal-cipher collision finder for `keyMasked`.
* `Cslib.IdealCipher.keyMaskedInputAdversary`: 2-query ideal-cipher collision finder for
  `keyMaskedInput`.

## Main results

* `Cslib.IdealCipher.isQueryBounded_keyMaskedAdversary`,
  `Cslib.IdealCipher.isQueryBounded_keyMaskedInputAdversary`: both finders make at most `2`
  ideal-cipher queries on every execution path.
* `Cslib.IdealCipher.keyMaskedAdversary_wins`,
  `Cslib.IdealCipher.keyMaskedInputAdversary_wins`: for any distinct keys `k1 ≠ k2` and target
  `y`, both finders win `collisionGame` with exact distribution `PMF.pure true`.
* `Cslib.IdealCipher.exists_collisionFinder_keyMasked`,
  `Cslib.IdealCipher.exists_collisionFinder_keyMaskedInput`: over any nontrivial finite additive
  group, there exists a `2`-query `CollisionFinder` winning `collisionGame` with probability `1`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.5.2,
  p. 301, and Exercise 8.11, p. 349.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1,
  Exercise 7.23(c).
-/

public section

namespace Cslib.IdealCipher

open Cslib.Crypto.BlockCipherCompression Cslib.OracleComp Cslib.Probability
  Cslib.RandomPermutation

variable {Block : Type}

/-- An explicit ideal-cipher collision finder for `keyMasked` (`h₄` with its two arguments swapped,
[BonehShoup2023], Section 8.5.2, p. 301 and Exercise 8.11, p. 349; [KatzLindell2020],
Exercise 7.23(c)) using two inverse queries with distinct keys `k1`, `k2` and target digest `y`. -/
def keyMaskedAdversary [Sub Block] (k1 k2 y : Block) :
    OracleComp (Spec Block Block) ((Block × Block) × (Block × Block)) := do
  let x1 ← query (k1, PermQuery.inverse (y - k1))
  let x2 ← query (k2, PermQuery.inverse (y - k2))
  return ((k1, x1), (k2, x2))

/-- `keyMaskedAdversary` makes at most `2` ideal-cipher queries on every execution path. -/
theorem isQueryBounded_keyMaskedAdversary [Sub Block] (k1 k2 y : Block) :
    IsQueryBounded (keyMaskedAdversary k1 k2 y) 2 :=
  IsCostBounded.bind (cost := fun _ => 1) (IsCostBounded.query _) fun _ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ =>
      IsCostBounded.pure _ 0

/-- For any distinct keys `k1 ≠ k2` and any target `y`, `keyMaskedAdversary k1 k2 y` wins
`collisionGame keyMasked` with exact distribution `PMF.pure true`. -/
theorem keyMaskedAdversary_wins [DecidableEq Block] [Fintype Block] [AddGroup Block]
    {k1 k2 : Block} (hk : k1 ≠ k2) (y : Block) :
    collisionGame (keyMasked (B := Block)) (keyMaskedAdversary k1 k2 y) = PMF.pure true := by
  unfold collisionGame keyMaskedAdversary lazyEvalPerm
  simp only [IdealCipher.complete_nil, interpret_bind, interpret_query, interpret_pure]
  simp [bind, StateT.bind, pure, StateT.pure, evalPerm, collides, keyMasked_symm, hk]

/-- Existential summary for `keyMasked` (`h₄` with its two arguments swapped) over any nontrivial
finite additive group: there is a `2`-query ideal-cipher collision finder winning with probability
`1`. -/
theorem exists_collisionFinder_keyMasked [DecidableEq Block] [Fintype Block] [AddGroup Block]
    [Nontrivial Block] :
    ∃ A : CollisionFinder Block Block,
      IsQueryBounded A 2 ∧ Pr[collisionGame (keyMasked (B := Block)) A] = 1 := by
  obtain ⟨k1, k2, hk⟩ := exists_pair_ne Block
  refine ⟨keyMaskedAdversary k1 k2 0, isQueryBounded_keyMaskedAdversary k1 k2 0, ?_⟩
  rw [keyMaskedAdversary_wins hk 0]
  simp

/-- An explicit ideal-cipher collision finder for `keyMaskedInput` (`h₅`, [BonehShoup2023],
Section 8.5.2, p. 301 and Exercise 8.11, p. 349) using two inverse queries with distinct keys
`k1` and `k2` and target digest `y`. -/
def keyMaskedInputAdversary [AddGroup Block] (k1 k2 y : Block) :
    OracleComp (Spec Block Block) ((Block × Block) × (Block × Block)) := do
  let x1 ← query (k1, PermQuery.inverse (y - k1))
  let x2 ← query (k2, PermQuery.inverse (y - k2))
  return ((k1, -k1 + x1), (k2, -k2 + x2))

/-- `keyMaskedInputAdversary` makes at most `2` ideal-cipher queries on every execution path. -/
theorem isQueryBounded_keyMaskedInputAdversary [AddGroup Block] (k1 k2 y : Block) :
    IsQueryBounded (keyMaskedInputAdversary k1 k2 y) 2 :=
  IsCostBounded.bind (cost := fun _ => 1) (IsCostBounded.query _) fun _ =>
    IsCostBounded.bind (IsCostBounded.query _) fun _ =>
      IsCostBounded.pure _ 0

/-- For any distinct keys `k1 ≠ k2` and any target `y`, `keyMaskedInputAdversary k1 k2 y` wins
`collisionGame keyMaskedInput` with exact distribution `PMF.pure true`. -/
theorem keyMaskedInputAdversary_wins [DecidableEq Block] [Fintype Block] [AddGroup Block]
    {k1 k2 : Block} (hk : k1 ≠ k2) (y : Block) :
    collisionGame (keyMaskedInput (B := Block)) (keyMaskedInputAdversary k1 k2 y) =
      PMF.pure true := by
  unfold collisionGame keyMaskedInputAdversary lazyEvalPerm
  simp only [IdealCipher.complete_nil, interpret_bind, interpret_query, interpret_pure]
  simp [bind, StateT.bind, pure, StateT.pure, evalPerm, collides, keyMaskedInput_symm, hk]

/-- Existential summary for `keyMaskedInput` (`h₅`) over any nontrivial finite additive group:
there is a `2`-query ideal-cipher collision finder winning with probability `1`. -/
theorem exists_collisionFinder_keyMaskedInput [DecidableEq Block] [Fintype Block] [AddGroup Block]
    [Nontrivial Block] :
    ∃ A : CollisionFinder Block Block,
      IsQueryBounded A 2 ∧ Pr[collisionGame (keyMaskedInput (B := Block)) A] = 1 := by
  obtain ⟨k1, k2, hk⟩ := exists_pair_ne Block
  refine ⟨keyMaskedInputAdversary k1 k2 0, isQueryBounded_keyMaskedInputAdversary k1 k2 0, ?_⟩
  rw [keyMaskedInputAdversary_wins hk 0]
  simp

end Cslib.IdealCipher
