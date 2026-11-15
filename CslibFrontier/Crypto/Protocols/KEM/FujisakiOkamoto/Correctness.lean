/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.PKE.ExplicitCoin

/-!
# Shared correctness facts for Fujisaki--Okamoto transforms

This module contains the PKE-level facts shared by the unsalted and salted FO correctness hops. A
coin cache is good when every cached honest encryption decrypts to its cached message.
`ExplicitCoinPKE.advantage_bind_keyGen_le` is the common key-mixture rule: fixed-key `CloseTo`
bounds proportional to the worst-message failure probability average to the exact
`loss * δ` two-world advantage bound under `ExplicitCoinPKE.DeltaCorrect δ`.

## Main definitions

* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GoodCache`: every cached message/coin pair decrypts
  correctly for a fixed key pair.

## Main results

* `Cslib.Crypto.Protocols.ExplicitCoinPKE.GoodCache.of_subset`: goodness is inherited by a
  subcache.
* `Cslib.Crypto.Protocols.ExplicitCoinPKE.advantage_bind_keyGen_le`: average a fixed-key
  correctness hop over key generation.
-/

public section

namespace Cslib.Crypto.Protocols

open Probability
open scoped ENNReal NNReal

namespace ExplicitCoinPKE

variable {PK SK M R CT : Type}

/-- Every cached message/coin pair decrypts correctly for a fixed PKE key pair. -/
@[expose] def GoodCache (P : ExplicitCoinPKE PK SK M R CT) (pk : PK) (sk : SK)
    (cache : List (M × R)) : Prop :=
  ∀ e ∈ cache, P.dec sk (P.encDet pk e.1 e.2) = some e.1

/-- A subcache of a good cache is good. -/
theorem GoodCache.of_subset {P : ExplicitCoinPKE PK SK M R CT} {pk : PK} {sk : SK}
    {cache cache' : List (M × R)} (h : P.GoodCache pk sk cache')
    (hsub : ∀ e ∈ cache, e ∈ cache') : P.GoodCache pk sk cache :=
  fun e he => h e (hsub e he)

/-- **Average a fixed-key FO correctness hop over PKE key generation.** If fixed-key real and
simulated games are within `loss` times that key pair's worst-message failure probability, then
`DeltaCorrect δ` bounds their key-averaged two-world advantage by `loss * δ`. -/
theorem advantage_bind_keyGen_le [Fintype M] [Nonempty M]
    (P : ExplicitCoinPKE PK SK M R CT) (real simulated : PK → SK → PMF Bool) (loss : ℕ)
    (hclose : ∀ pk sk, CloseTo (real pk sk) (simulated pk sk)
      ((loss : ℝ≥0∞) * ENNReal.ofReal (P.keyPairMaxFailProb pk sk)))
    {δ : ℝ} (hδ : P.DeltaCorrect δ) :
    (Game.advantage
        ((ProbComp.eval P.keyGen).bind fun keys => real keys.1 keys.2)
        ((ProbComp.eval P.keyGen).bind fun keys => simulated keys.1 keys.2) : ℝ) ≤
      (loss : ℝ) * δ := by
  set E : ℝ≥0∞ := P.keyGen.expect fun keys =>
    ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2) with hE
  have hmix : CloseTo
      ((ProbComp.eval P.keyGen).bind fun keys => real keys.1 keys.2)
      ((ProbComp.eval P.keyGen).bind fun keys => simulated keys.1 keys.2)
      ((loss : ℝ≥0∞) * E) := by
    refine (CloseTo.bind_right_tsum _ (err := fun keys : PK × SK =>
      (loss : ℝ≥0∞) * ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2))
      fun keys _ => hclose keys.1 keys.2).mono (le_of_eq ?_)
    rw [hE, ProbComp.expect, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun keys => ?_
    ring
  have hadv := Game.closeTo_iff_coe_advantage_le.mp hmix
  have hEtop : E ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    rw [hE, ProbComp.expect]
    calc ∑' keys, ProbComp.eval P.keyGen keys *
          ENNReal.ofReal (P.keyPairMaxFailProb keys.1 keys.2)
        ≤ ∑' keys, ProbComp.eval P.keyGen keys * 1 := by
          gcongr with keys
          exact ENNReal.ofReal_le_one.mpr (P.keyPairMaxFailProb_le_one keys.1 keys.2)
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  calc (Game.advantage
        ((ProbComp.eval P.keyGen).bind fun keys => real keys.1 keys.2)
        ((ProbComp.eval P.keyGen).bind fun keys => simulated keys.1 keys.2) : ℝ)
      = ((Game.advantage
          ((ProbComp.eval P.keyGen).bind fun keys => real keys.1 keys.2)
          ((ProbComp.eval P.keyGen).bind fun keys => simulated keys.1 keys.2) : ℝ≥0∞)).toReal := by
            rw [ENNReal.coe_toReal]
    _ ≤ ((loss : ℝ≥0∞) * E).toReal :=
      ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hEtop) hadv
    _ = (loss : ℝ) * E.toReal := by rw [ENNReal.toReal_mul, ENNReal.toReal_natCast]
    _ ≤ (loss : ℝ) * δ := mul_le_mul_of_nonneg_left hδ (Nat.cast_nonneg _)

end ExplicitCoinPKE

end Cslib.Crypto.Protocols
