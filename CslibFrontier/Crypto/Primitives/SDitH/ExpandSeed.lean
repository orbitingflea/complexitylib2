/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SDitH.TweakSalt
public import CslibFrontier.Init

/-!
# SDitH seed expansion

For Categories I and V, SDitH v3 expands one seed into its two GGM-tree children by encrypting
two domain-separated plaintexts under that seed. The plaintexts use the even and odd 24-bit
tweaks `2 * idx` and `2 * idx + 1`, respectively, with the seed-expansion tag set to `true`.

This module formalizes only the two-call `ExpandSeed` procedure. The modified block cipher
`Enc*` is an explicit function parameter: this layer neither instantiates AES or Rijndael nor
asserts a pseudorandomness or ideal-cipher property. It does not build the full GGM tree,
`CommitSeed`, the one-tree BAVC, or the SDitH protocol.

The specification passage attributes this procedure only to Categories I and V. The generalized
primitive-parametric API also accommodates the reference implementation's 192-bit Category III
path using truncated Rijndael-256-256, but that compatibility observation is not a Category III
claim from the cited passage.

At the function level, `expandSeed` makes exactly two calls to `encStar` and materializes exactly
two tweaked salts. This is not a native implementation or resource certificate. Later consumers
must account for those calls, the full `securityBits`-bit plaintexts, retained program-description
size, and all time, space, randomness, query, output, and reduction resources.

## Main definitions

* `Cslib.Crypto.SDitH.expandSeedLeftTweak`: the 24-bit even child tweak.
* `Cslib.Crypto.SDitH.expandSeedRightTweak`: the 24-bit odd child tweak.
* `Cslib.Crypto.SDitH.expandSeed`: the source's two-call seed expansion.

## Main results

* `Cslib.Crypto.SDitH.expandSeed_fst`: the left child is the even-tweak encryption.
* `Cslib.Crypto.SDitH.expandSeed_snd`: the right child is the odd-tweak encryption.
* `Cslib.Crypto.SDitH.expandSeed_plaintexts_ne`: the two source plaintexts are distinct at
  standard salt widths.

## References

* [*The Syndrome Decoding in the Head Signature Scheme*, v3.0, Section 3.2.2,
  “Seed expansion (GGM tree),” p. 18][SDitH2026]
-/

public section

namespace Cslib.Crypto.SDitH

/-- The even 24-bit tweak used for the left child of source node `idx`.

Restricting `idx` to 23 bits makes both source expressions `2 * idx` and `2 * idx + 1` valid
24-bit tweaks without modular wraparound. -/
@[expose]
def expandSeedLeftTweak (idx : Fin (2 ^ 23)) : Fin (2 ^ 24) :=
  ⟨2 * idx.val, by omega⟩

/-- The odd 24-bit tweak used for the right child of source node `idx`. -/
@[expose]
def expandSeedRightTweak (idx : Fin (2 ^ 23)) : Fin (2 ^ 24) :=
  ⟨2 * idx.val + 1, by omega⟩

@[simp]
theorem expandSeedLeftTweak_val (idx : Fin (2 ^ 23)) :
    (expandSeedLeftTweak idx : Nat) = 2 * idx.val :=
  rfl

@[simp]
theorem expandSeedRightTweak_val (idx : Fin (2 ^ 23)) :
    (expandSeedRightTweak idx : Nat) = 2 * idx.val + 1 :=
  rfl

/-- The source's even and odd child tweaks are distinct. -/
theorem expandSeedLeftTweak_ne_rightTweak (idx : Fin (2 ^ 23)) :
    expandSeedLeftTweak idx ≠ expandSeedRightTweak idx := by
  intro h
  have hval := congrArg Fin.val h
  simp only [expandSeedLeftTweak_val, expandSeedRightTweak_val] at hval
  omega

/-- SDitH v3 Section 3.2.2, `ExpandSeed`, stated by the source for Categories I and V.

The first `encStar` argument is the key/seed and the second is the plaintext. The explicit
grinding variant selects Algorithm 5's high-bit layout for the calling parameter set. The
primitive-parametric definition also fits the reference implementation's 192-bit Category III
path using truncated Rijndael-256-256; that is an implementation compatibility observation, not
a Category III attribution to this source passage. -/
@[expose]
def expandSeed {securityBits : Nat}
    (encStar : BitString securityBits → BitString securityBits → BitString securityBits)
    (variant : GrindingVariant) (salt seed : BitString securityBits) (idx : Fin (2 ^ 23)) :
    BitString securityBits × BitString securityBits :=
  (encStar seed (tweakSalt variant salt (expandSeedLeftTweak idx) true),
    encStar seed (tweakSalt variant salt (expandSeedRightTweak idx) true))

/-- The left output of `expandSeed` is the encryption at the even child tweak. -/
@[simp]
theorem expandSeed_fst {securityBits : Nat}
    (encStar : BitString securityBits → BitString securityBits → BitString securityBits)
    (variant : GrindingVariant) (salt seed : BitString securityBits) (idx : Fin (2 ^ 23)) :
    (expandSeed encStar variant salt seed idx).1 =
      encStar seed (tweakSalt variant salt (expandSeedLeftTweak idx) true) :=
  rfl

/-- The right output of `expandSeed` is the encryption at the odd child tweak. -/
@[simp]
theorem expandSeed_snd {securityBits : Nat}
    (encStar : BitString securityBits → BitString securityBits → BitString securityBits)
    (variant : GrindingVariant) (salt seed : BitString securityBits) (idx : Fin (2 ^ 23)) :
    (expandSeed encStar variant salt seed idx).2 =
      encStar seed (tweakSalt variant salt (expandSeedRightTweak idx) true) :=
  rfl

/-- At widths where Algorithm 5's tweak and tag coordinates are disjoint, `ExpandSeed` supplies
distinct plaintexts to its two block-cipher calls. This does not assert that the encrypted child
seeds are distinct. -/
theorem expandSeed_plaintexts_ne (variant : GrindingVariant) {securityBits : Nat}
    (hsecurity : 26 ≤ securityBits) (salt : BitString securityBits) (idx : Fin (2 ^ 23)) :
    tweakSalt variant salt (expandSeedLeftTweak idx) true ≠
      tweakSalt variant salt (expandSeedRightTweak idx) true := by
  intro h
  have hpair : (expandSeedLeftTweak idx, true) = (expandSeedRightTweak idx, true) :=
    (tweakSalt_injective variant hsecurity salt) h
  exact expandSeedLeftTweak_ne_rightTweak idx (congrArg Prod.fst hpair)

end Cslib.Crypto.SDitH
