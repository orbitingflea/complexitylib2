/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.ElGamal
public import CslibFrontier.Crypto.Computational.KeyDerivation
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Tactic.PolyTime

/-!
# Group key derivation as an instance of the general key-derivation game

`PrimeOrderGroupFamily.SecureKDF` ([BonehShoup2023], Section 11.5.2, Attack Game 11.3, p. 448, and
Definition 11.5, p. 449) is the group-specialized key-derivation assumption used by Hashed ElGamal
(`CslibFrontier/Crypto/Computational/ElGamal.lean`): a distinguisher receives the group description
`d ← setup n`, two independent group elements `a • g` and `b • g`, and either
`H (d, F.encode d (c • g))` for an independent uniform `c` or an independent uniform `msgLen n`-bit
word.

This module shows (`secureKDF_iff_keyDerivation`) that `F.SecureKDF setup H msgLen` is an instance
of `KeyDerivation.Secure`: the secret `F.kdfSecret setup n` packages a random `F.DDHInput` drawing
`d ← setup n` and independent uniform `a, b, c` (via `F.ddhRandomTupleLaw`), the public side
information is `DDHInput.toCDHInput`, the derived key is
`fun x => H (x.groupParameters, F.encode x.groupParameters x.candidateShared)`, and the ideal key
law is `BitString.uniformList (msgLen n)`. Combined with
`PrimeOrderGroupFamily.secureKDF_linearHashKDF`
(`CslibFrontier/Crypto/Computational/ElGamal/KDF.lean`), this gives an instance of
`KeyDerivation.Secure` with no hardness assumption under `F.LinearHashKDFConditions`, via the
leftover hash lemma.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.kdfSecret`: the secret distribution drawing `d ← setup n` and
  a random DDH triple via `F.ddhRandomTupleLaw d` as an `F.DDHInput`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.secureKDF_iff_keyDerivation`: `F.SecureKDF setup H msgLen` is
  equivalent to `KeyDerivation.Secure` for `F.kdfSecret setup`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 11.5.2 (Attack Game 11.3 and Definition 11.5, pp. 448–449).
-/

public section

open Cslib Probability Turing.MultiTapeTM

namespace Cslib.Crypto.PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-- The law of the secret: `d ← setup n` and a random DDH triple via `F.ddhRandomTupleLaw d`. -/
noncomputable def kdfSecret (setup : ℕ → PMF F.Desc) (n : ℕ) : PMF F.DDHInput := do
  let d ← setup n
  let (u, v, w) ← F.ddhRandomTupleLaw d
  return ⟨⟨n, d, u, v⟩, w⟩

/-- `SecureKDF` is `KeyDerivation.Secure` for the secret `kdfSecret`, the CDH input as public
information, and the key `H (d, encode w)`. -/
theorem secureKDF_iff_keyDerivation (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (msgLen : ℕ → ℕ) :
    F.SecureKDF setup H msgLen ↔
      KeyDerivation.Secure F.encCDHInput encBits (F.kdfSecret setup) DDHInput.toCDHInput
        (fun x => H (x.groupParameters, F.encode x.groupParameters x.candidateShared))
        (fun n => Cslib.BitString.uniformList (msgLen n)) := by
  constructor
  · intro h D hD
    have hD' : KDFDistinguisher.IsPPT (F := F) (fun n d u v key => D n ⟨n, d, u, v⟩ key) :=
      IsPPTOn.preprocess hD
        (prepare := fun x : F.KDFInput => (x.secParam, x.toCDHInput, x.key)) (by fun_prop)
    refine (h _ hD').congr fun n => ?_
    simp only [kdfRealGame, kdfIdealGame, KeyDerivation.realGame, KeyDerivation.idealGame,
      KeyDerivation.realOutput, KeyDerivation.idealOutput, kdfSecret, ddhRandomTupleLaw,
      pmf_norm, PMF.bind_const]
  · intro h D hD
    have hD' : KeyDerivation.Distinguisher.IsPPT F.encCDHInput encBits
        (fun _ x key => D x.secParam x.groupParameters x.leftPublic x.rightPublic key) :=
      IsPPTOn.preprocess hD
        (prepare := fun p : ℕ × F.CDHInput × List Bool => (⟨p.2.1, p.2.2⟩ : F.KDFInput))
        (by fun_prop)
    refine (h _ hD').congr fun n => ?_
    simp only [kdfRealGame, kdfIdealGame, KeyDerivation.realGame, KeyDerivation.idealGame,
      KeyDerivation.realOutput, KeyDerivation.idealOutput, kdfSecret, ddhRandomTupleLaw,
      pmf_norm, PMF.bind_const]

end Cslib.Crypto.PrimeOrderGroupFamily
