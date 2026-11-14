/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SDitH.ExpandSeed

/-! Checked 128-bit clients for SDitH v3 Section 3.2.2, `ExpandSeed`. -/

public section

namespace SDitHExpandSeedTests

open Cslib Cslib.Crypto.SDitH

/-- A concrete toy keyed permutation used only to exercise both source calls. -/
def xorEnc (key plaintext : BitString 128) : BitString 128 :=
  key + plaintext

def zeroSalt : BitString 128 := fun _ => false

def lowSeed : BitString 128 := fun i => decide (i.val = 0)

def nodeFive : Fin (2 ^ 23) := ⟨5, by norm_num⟩

example : (expandSeedLeftTweak nodeFive : Nat) = 10 := by decide +kernel

example : (expandSeedRightTweak nodeFive : Nat) = 11 := by decide +kernel

example :
    (expandSeed xorEnc .hashBased zeroSalt lowSeed nodeFive).1 =
      xorEnc lowSeed (tweakSalt .hashBased zeroSalt (expandSeedLeftTweak nodeFive) true) := by
  rw [expandSeed_fst]

example :
    (expandSeed xorEnc .hashBased zeroSalt lowSeed nodeFive).2 =
      xorEnc lowSeed (tweakSalt .hashBased zeroSalt (expandSeedRightTweak nodeFive) true) := by
  rw [expandSeed_snd]

-- The even and odd plaintexts differ in their low bit; the toy key flips that bit in both.
example : (expandSeed xorEnc .hashBased zeroSalt lowSeed nodeFive).1 0 = true := by
  decide +kernel

example : (expandSeed xorEnc .hashBased zeroSalt lowSeed nodeFive).2 0 = false := by
  decide +kernel

example :
    tweakSalt .cipherBased zeroSalt (expandSeedLeftTweak nodeFive) true ≠
      tweakSalt .cipherBased zeroSalt (expandSeedRightTweak nodeFive) true := by
  exact expandSeed_plaintexts_ne .cipherBased (by norm_num) zeroSalt nodeFive

end SDitHExpandSeedTests
