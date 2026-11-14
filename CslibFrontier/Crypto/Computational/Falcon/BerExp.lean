/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Probability.PMF.Bool

/-!
# Falcon v1.2 BerExp threshold distribution

Falcon v1.2 Algorithm 14 computes a 64-bit integer threshold `z` from floating-point inputs, then
accepts exactly when a uniform 64-bit value is strictly below `z`. This module isolates that exact
distributional boundary after `z` has already been computed. The resulting acceptance mass is
`z / 2^64` for every possible threshold, including both endpoints of the unsigned range.

`berExpThresholdCoin` uses the shared exact 64-fair-bit sampler. It is denotationally equivalent to
Algorithm 14's threshold comparison, but does not model the reference implementation's lazy
one-to-eight-byte consumption trace. It also does not formalize `ApproxExp`, bound floating-point
error, construct `BaseSampler` or `SamplerZ`, prove a Gaussian law or termination, certify native
resources, or establish a security reduction or the still-developing FN-DSA / FIPS 206 interface.
NIST lists that interface as under development as of 13 November 2026 ([NISTPQC2026]).

## Main definitions

* `Cslib.Crypto.Falcon.BerExpThreshold`: an unsigned 64-bit acceptance threshold.
* `Cslib.Crypto.Falcon.berExpThresholdAccepts`: the deterministic strict comparison.
* `Cslib.Crypto.Falcon.berExpThresholdCoin`: the exact fair-bit threshold experiment.

## Main results

* `Cslib.Crypto.Falcon.berExpThresholdAccepts_eq_true_iff`: deterministic acceptance is exactly
  strict comparison with the threshold.
* `Cslib.Crypto.Falcon.eval_berExpThresholdCoin_true`: acceptance mass is exactly `z / 2^64`.
* `Cslib.Crypto.Falcon.eval_berExpThresholdCoin_true_toReal`,
  `Cslib.Crypto.Falcon.eval_berExpThresholdCoin_false_toReal`: real-valued acceptance and
  rejection masses.

## References

* [Falcon team, *Falcon: Fast-Fourier Lattice-based Compact Signatures over NTRU*, Round 3
  submission, version 1.2][Falcon2020], Section 3.9.3, Algorithm 14, lines 4–10.
* Pinned [Falcon2020] archive,
  `Reference_Implementation/falcon512/falcon512int/sign.c::BerExp`: threshold assignment at line
  1074 and lazy comparison at lines 1082–1087.
* [National Institute of Standards and Technology, *Post-Quantum Cryptography
  Standardization*][NISTPQC2026].
-/

public section

namespace Cslib.Crypto.Falcon

open Probability

/-- The 64-bit unsigned integer threshold produced before Algorithm 14's uniform comparison. -/
abbrev BerExpThreshold := Fin (2 ^ 64)

/-- Algorithm 14 accepts a uniform word exactly when it is strictly below the threshold.

The probabilistic experiment supplies a sample below `2 ^ 64`; accepting a natural number keeps
this predicate as the single comparison implementation used by both the experiment and direct
clients. -/
@[expose] def berExpThresholdAccepts
    (threshold : BerExpThreshold) (sample : ℕ) : Bool :=
  decide (sample < threshold.val)

/-- The deterministic threshold comparison accepts exactly below the threshold. -/
@[simp] theorem berExpThresholdAccepts_eq_true_iff
    (threshold : BerExpThreshold) (sample : ℕ) :
    berExpThresholdAccepts threshold sample = true ↔ sample < threshold.val := by
  simp [berExpThresholdAccepts]

/-- The deterministic threshold comparison rejects exactly at or above the threshold. -/
@[simp] theorem berExpThresholdAccepts_eq_false_iff
    (threshold : BerExpThreshold) (sample : ℕ) :
    berExpThresholdAccepts threshold sample = false ↔ threshold.val ≤ sample := by
  simp [berExpThresholdAccepts]

/-- The exact distributional threshold step of Falcon v1.2 `BerExp`.

This draws a fixed 64 fair bits through the shared sampler. The reference implementation compares
successive bytes lazily; that operational consumption trace is deliberately outside this
denotational interface. -/
noncomputable def berExpThresholdCoin (threshold : BerExpThreshold) : ProbComp Bool := do
  let sample ← ProbComp.sampleBinaryNat 64
  return berExpThresholdAccepts threshold sample

/-- Algorithm 14's threshold step accepts with exact mass `z / 2^64`. -/
theorem eval_berExpThresholdCoin_true (threshold : BerExpThreshold) :
    ProbComp.eval (berExpThresholdCoin threshold) true =
      (threshold.val : ENNReal) / 2 ^ 64 := by
  simp only [berExpThresholdCoin, berExpThresholdAccepts, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_sampleBinaryNat, PMF.bind_map]
  change ((PMF.uniformOfFintype (Fin (2 ^ 64))).bind
    (PMF.pure ∘ fun i => decide (i.val < threshold.val))) true = _
  rw [PMF.bind_pure_comp, Cslib.Probability.uniformFin_decide_lt,
    Nat.min_eq_right threshold.isLt.le]
  norm_num

/-- Real-valued form of the exact `BerExp` threshold acceptance mass. -/
theorem eval_berExpThresholdCoin_true_toReal (threshold : BerExpThreshold) :
    (ProbComp.eval (berExpThresholdCoin threshold) true).toReal =
      (threshold.val : ℝ) / 2 ^ 64 := by
  rw [eval_berExpThresholdCoin_true, ENNReal.toReal_div]
  simp

/-- Rejection has the complementary real mass `1 - z / 2^64`. -/
theorem eval_berExpThresholdCoin_false_toReal (threshold : BerExpThreshold) :
    (ProbComp.eval (berExpThresholdCoin threshold) false).toReal =
      1 - (threshold.val : ℝ) / 2 ^ 64 := by
  rw [PMF.toReal_false_eq_one_sub, eval_berExpThresholdCoin_true_toReal]

end Cslib.Crypto.Falcon
