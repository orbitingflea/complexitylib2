/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Basic

/-!
# Compression functions from block ciphers

[KatzLindell2020], Section 7.3.1, builds a compression function from a block cipher
`F : K × B → B`, where each `F k` is a permutation of the block space `B` whose inverse is also
efficiently computable. The *Davies–Meyer* construction (Figure 7.11) is
`h(k, x) = F_k(x) ⊕ x`; Theorem 7.5 shows it is collision resistant when `F` is an ideal cipher.

Here we record the explicit attacks that rule out other natural choices, using only that each
`F k` is a permutation with an inverse:

* `h(k, x) = F_k(x)` ([KatzLindell2020], Exercise 7.23(a)), `h(k, x) = F_k(x) ⊕ k`
  ([KatzLindell2020], Exercise 7.23(c); equivalently `h₄` of [BonehShoup2023], Section 8.5.2,
  p. 301, with its two arguments swapped), and `h₅(k, x) = F_k(k ⊕ x) ⊕ k` ([BonehShoup2023],
  Section 8.5.2, p. 301) have preimages computable with one inverse query, so any two distinct
  keys give a collision (for `h₄` and `h₅`, [BonehShoup2023], Exercise 8.11, p. 349);
* Davies–Meyer sends every fixed point `F_k(x) = x` to `0`, so two distinct fixed points collide
  ([KatzLindell2020], Exercise 7.24).

The block space is any additive group (for bits, `BitString n`, where `+` is exclusive or); the
attacks of Exercise 7.23 and Exercise 8.11 hold over every additive group, while the fixed-point
attack uses `x + x = 0` on bit strings. The ideal-cipher bound of Theorem 7.5 and Exercise 7.23(b),
`h(k, x) = F_k(x) ⊕ k ⊕ x`, are not formalized here; for the 2-query ideal-cipher collision
finders on `keyMasked` and `keyMaskedInput`, see
`CslibFrontier.Crypto.Primitives.IdealCipher.CompressionVariants`.

## Main definitions

* `Cslib.Crypto.BlockCipherCompression.daviesMeyer`: the Davies–Meyer compression function.
* `Cslib.Crypto.BlockCipherCompression.cipherOutput`,
  `Cslib.Crypto.BlockCipherCompression.keyMasked`,
  `Cslib.Crypto.BlockCipherCompression.keyMaskedInput`: the compression functions of
  [KatzLindell2020], Exercise 7.23(a), (c) and [BonehShoup2023], Section 8.5.2 (`h₄`, `h₅`).

## Main results

* `Cslib.Crypto.BlockCipherCompression.cipherOutput_collision`,
  `Cslib.Crypto.BlockCipherCompression.keyMasked_collision`,
  `Cslib.Crypto.BlockCipherCompression.keyMaskedInput_collision`: explicit collisions from two
  distinct keys and inverse queries.
* `Cslib.Crypto.BlockCipherCompression.daviesMeyer_collision_of_fixedPoints`: two distinct fixed
  points give a Davies–Meyer collision.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 8.5.2,
  p. 301, and Exercise 8.11, p. 349.
* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 7.3.1,
  Figure 7.11, Theorem 7.5, Exercises 7.23 and 7.24.
-/

public section

namespace Cslib.Crypto.BlockCipherCompression

variable {K B : Type*}

/-! ### The compression functions -/

/-- The Davies–Meyer compression function `h(k, x) = F_k(x) + x` ([KatzLindell2020],
Section 7.3.1, Figure 7.11). -/
@[expose]
def daviesMeyer [Add B] (F : K → Equiv.Perm B) (p : K × B) : B :=
  F p.1 p.2 + p.2

/-- The compression function `h(k, x) = F_k(x)` of [KatzLindell2020], Exercise 7.23(a). -/
@[expose]
def cipherOutput (F : K → Equiv.Perm B) (p : K × B) : B :=
  F p.1 p.2

/-- The compression function `h(k, x) = F_k(x) + k` of [KatzLindell2020], Exercise 7.23(c); keys
and blocks have the same type. Up to swapping its two arguments, this is `h₄` of
[BonehShoup2023], Section 8.5.2, p. 301. -/
@[expose]
def keyMasked [Add B] (F : B → Equiv.Perm B) (p : B × B) : B :=
  F p.1 p.2 + p.1

/-- The compression function `h₅(k, x) = F_k(k + x) + k` ([BonehShoup2023], Section 8.5.2,
p. 301); keys and blocks have the same type. Over bit strings (`BitString n`), `+` is exclusive
or, so this matches `h₅(x, y) := E(x, x ⊕ y) ⊕ x`. -/
@[expose]
def keyMaskedInput [Add B] (F : B → Equiv.Perm B) (p : B × B) : B :=
  F p.1 (p.1 + p.2) + p.1

/-! ### Inverse-query attacks on Exercise 7.23(a), (c) and Exercise 8.11 -/

/-- One inverse query finds a preimage of `y` under `h(k, x) = F_k(x)`, for any key `k`. -/
@[simp]
theorem cipherOutput_symm (F : K → Equiv.Perm B) (k : K) (y : B) :
    cipherOutput F (k, (F k).symm y) = y := by
  simp [cipherOutput]

/-- **Exercise 7.23(a)** ([KatzLindell2020], Section 7.3.1): for distinct keys `k ≠ k'` and any
target `y`, the inputs `(k, F_k⁻¹(y))` and `(k', F_{k'}⁻¹(y))` are distinct and collide under
`h(k, x) = F_k(x)`. -/
theorem cipherOutput_collision (F : K → Equiv.Perm B) {k k' : K} (hk : k ≠ k') (y : B) :
    (k, (F k).symm y) ≠ (k', (F k').symm y) ∧
      cipherOutput F (k, (F k).symm y) = cipherOutput F (k', (F k').symm y) :=
  ⟨fun h => hk (Prod.ext_iff.1 h).1, by simp⟩

/-- One inverse query finds a preimage of `y` under `h(k, x) = F_k(x) + k`: take
`x = F_k⁻¹(y - k)`. -/
@[simp]
theorem keyMasked_symm [AddGroup B] (F : B → Equiv.Perm B) (k y : B) :
    keyMasked F (k, (F k).symm (y - k)) = y := by
  simp [keyMasked]

/-- **Exercise 7.23(c)** ([KatzLindell2020], Section 7.3.1; also the `h₄` part of
[BonehShoup2023], Exercise 8.11, p. 349): for distinct keys `k ≠ k'` and any target `y`, the
inputs `(k, F_k⁻¹(y - k))` and `(k', F_{k'}⁻¹(y - k'))` are distinct and collide under
`h(k, x) = F_k(x) + k`. -/
theorem keyMasked_collision [AddGroup B] (F : B → Equiv.Perm B) {k k' : B} (hk : k ≠ k')
    (y : B) :
    (k, (F k).symm (y - k)) ≠ (k', (F k').symm (y - k')) ∧
      keyMasked F (k, (F k).symm (y - k)) = keyMasked F (k', (F k').symm (y - k')) :=
  ⟨fun h => hk (Prod.ext_iff.1 h).1, by simp⟩

/-- `keyMaskedInput` is `keyMasked` composed with the map `(k, x) ↦ (k, k + x)`. -/
theorem keyMaskedInput_eq_keyMasked [Add B] (F : B → Equiv.Perm B) (k x : B) :
    keyMaskedInput F (k, x) = keyMasked F (k, k + x) := rfl

/-- One inverse query finds a preimage of `y` under `h₅(k, x) = F_k(k + x) + k`: take
`x = -k + F_k⁻¹(y - k)`. -/
@[simp]
theorem keyMaskedInput_symm [AddGroup B] (F : B → Equiv.Perm B) (k y : B) :
    keyMaskedInput F (k, -k + (F k).symm (y - k)) = y := by
  rw [keyMaskedInput_eq_keyMasked, add_neg_cancel_left, keyMasked_symm]

/-- **Exercise 8.11** ([BonehShoup2023], Exercise 8.11, p. 349; `h₅` is defined in
Section 8.5.2, p. 301): for distinct keys `k ≠ k'` and any target `y`, the inputs
`(k, -k + F_k⁻¹(y - k))` and `(k', -k' + F_{k'}⁻¹(y - k'))` are distinct and collide under
`keyMaskedInput` (`h₅`). -/
theorem keyMaskedInput_collision [AddGroup B] (F : B → Equiv.Perm B) {k k' : B} (hk : k ≠ k')
    (y : B) :
    (k, -k + (F k).symm (y - k)) ≠ (k', -k' + (F k').symm (y - k')) ∧
      keyMaskedInput F (k, -k + (F k).symm (y - k)) =
        keyMaskedInput F (k', -k' + (F k').symm (y - k')) :=
  ⟨fun h => hk (Prod.ext_iff.1 h).1, by simp⟩

/-! ### Fixed points and Davies–Meyer (Exercise 7.24) -/

/-- Over any additive group, Davies–Meyer outputs `0` exactly on the inputs with
`F_k(x) = -x`. -/
theorem daviesMeyer_eq_zero_iff [AddGroup B] (F : K → Equiv.Perm B) (k : K) (x : B) :
    daviesMeyer F (k, x) = 0 ↔ F k x = -x :=
  add_eq_zero_iff_eq_neg

/-- On bit strings, Davies–Meyer outputs `0` exactly on the fixed points `F_k(x) = x`. -/
theorem daviesMeyer_eq_zero_iff_fixed {n : ℕ} (F : K → Equiv.Perm (BitString n)) (k : K)
    (x : BitString n) : daviesMeyer F (k, x) = 0 ↔ F k x = x := by
  constructor
  · intro h
    simpa [daviesMeyer] using congrArg (· + x) h
  · intro h
    simp [daviesMeyer, h]

/-- **Exercise 7.24** ([KatzLindell2020], Section 7.3.1): two distinct fixed points
`F_k(x) = x` and `F_{k'}(x') = x'` (possibly for the same key) collide under Davies–Meyer, both
hashing to `0`. -/
theorem daviesMeyer_collision_of_fixedPoints {n : ℕ} (F : K → Equiv.Perm (BitString n))
    {k k' : K} {x x' : BitString n} (hx : F k x = x) (hx' : F k' x' = x') :
    daviesMeyer F (k, x) = daviesMeyer F (k', x') :=
  ((daviesMeyer_eq_zero_iff_fixed F k x).2 hx).trans
    ((daviesMeyer_eq_zero_iff_fixed F k' x').2 hx').symm

end Cslib.Crypto.BlockCipherCompression
