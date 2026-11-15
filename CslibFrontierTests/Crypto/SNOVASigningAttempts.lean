/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.SNOVA.SigningAttempts

/-!
# Tests for SNOVA's signing-attempt schedule

These examples catch the two source-level off-by-one hazards: scheduling either sentinel byte or
modeling Algorithm 17 as 255 attempted vinegar systems instead of 254.
-/

namespace Cslib.Crypto.SNOVA

example : signingAttemptCounters.length = 254 := by simp

example : signingAttemptCounters.length ≠ 255 := by simp

example : (0 : Fin 256) ∉ signingAttemptCounters := by simp

example : (255 : Fin 256) ∉ signingAttemptCounters := by
  rw [mem_signingAttemptCounters_iff]
  change ¬(1 ≤ (255 : ℕ) ∧ (255 : ℕ) < 255)
  omega

example : (1 : Fin 256) ∈ signingAttemptCounters := by simp

example : (254 : Fin 256) ∈ signingAttemptCounters := by
  rw [mem_signingAttemptCounters_iff]
  change 1 ≤ (254 : ℕ) ∧ (254 : ℕ) < 255
  omega

example : signingAttemptCounters[0]'(by simp) = (1 : Fin 256) :=
  first_signingAttemptCounter

example : signingAttemptCounters[253]'(by simp) = (254 : Fin 256) :=
  last_signingAttemptCounter

end Cslib.Crypto.SNOVA
