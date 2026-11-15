/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# SNOVA's bounded signing-attempt schedule

SNOVA derives fresh vinegar variables for a signing attempt from a one-byte counter `numsig`.
Algorithm 17 of [SNOVA2026] increments this counter before an attempt and returns failure when the
incremented counter is `255`, before deriving those variables. Algorithm 14 uses the surviving
counter value as part of the SHAKE256 input. Thus a signing invocation tries exactly the increasing
bytes `1, ..., 254`; neither `0` nor the failure sentinel `255` is tried.

This module records only that source-level schedule. It makes no claim about the distribution or
independence of the resulting linear systems, their solvability, or SNOVA's signing-failure
probability. In particular, a loop with 254 attempted counters does not by itself justify the
reference implementation's informal probability estimate.

## Main definitions

* `Cslib.Crypto.SNOVA.signingAttemptCounters`: the exact attempted counter bytes.

## Main results

* `Cslib.Crypto.SNOVA.length_signingAttemptCounters`: exactly 254 attempts are scheduled.
* `Cslib.Crypto.SNOVA.getElem_signingAttemptCounters`: attempt index `i` uses byte `i + 1`.
* `Cslib.Crypto.SNOVA.mem_signingAttemptCounters_iff`: exactly bytes 1 through 254 occur.
* `Cslib.Crypto.SNOVA.pairwise_lt_signingAttemptCounters`: the schedule is strictly increasing.
* `Cslib.Crypto.SNOVA.nodup_signingAttemptCounters`: no counter byte is attempted twice.
* `Cslib.Crypto.SNOVA.first_signingAttemptCounter`: the first attempted counter is 1.
* `Cslib.Crypto.SNOVA.last_signingAttemptCounter`: the last attempted counter is 254.

## References

* [Lih-Chung Wang et al., *SNOVA: Proposal for NIST PQC: Additional Digital Signature Schemes*,
  version 3.0][SNOVA2026], Algorithms 14 and 17, pp. 23 and 25; PDF SHA-256
  `67bf2e5414001d4562f76fff77cbc72b6c997ff2cffef3b5180a886359892898`.
* SNOVA Round-3 reference implementation, commit
  `d88ef38bfa28587372f29f10482aa208c703f1aa`, `src/snova_ref.c`.
-/

public section

namespace Cslib.Crypto.SNOVA

/-- The one-byte `numsig` values for which SNOVA Algorithm 17 actually attempts to solve a
vinegar-dependent oil system. Byte `255` is the pre-attempt failure sentinel. -/
@[expose] def signingAttemptCounters : List (Fin 256) :=
  (List.finRange 254).map fun i => ⟨i.val + 1, by omega⟩

/-- SNOVA Algorithm 17 schedules exactly 254 attempts. -/
@[simp]
theorem length_signingAttemptCounters : signingAttemptCounters.length = 254 := by
  simp only [signingAttemptCounters, List.length_map, List.length_finRange]

/-- The attempt at zero-based index `i` uses counter byte `i + 1`. -/
theorem getElem_signingAttemptCounters (i : ℕ) (hi : i < signingAttemptCounters.length) :
    signingAttemptCounters[i].val = i + 1 := by
  simp only [signingAttemptCounters, List.length_map, List.length_finRange] at hi
  simp only [signingAttemptCounters, List.getElem_map, List.getElem_finRange, Fin.val_cast,
    Fin.val_mk]

/-- A byte occurs in SNOVA's signing-attempt schedule exactly when it is between `1` and `254`.
This excludes both the initial counter `0` and the failure sentinel `255`. -/
@[simp]
theorem mem_signingAttemptCounters_iff (counter : Fin 256) :
    counter ∈ signingAttemptCounters ↔ 1 ≤ counter.val ∧ counter.val < 255 := by
  simp only [signingAttemptCounters, List.mem_map, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, rfl⟩
    change 1 ≤ i.val + 1 ∧ i.val + 1 < 255
    omega
  · rintro ⟨hpos, hlt⟩
    let i : Fin 254 := ⟨counter.val - 1, by omega⟩
    refine ⟨i, ?_⟩
    apply Fin.ext
    simp only [i]
    omega

/-- SNOVA's attempted counter bytes occur in strictly increasing order. -/
theorem pairwise_lt_signingAttemptCounters : signingAttemptCounters.Pairwise (· < ·) := by
  dsimp only [signingAttemptCounters]
  apply (List.pairwise_lt_finRange 254).map
  intro a b hab
  change a.val + 1 < b.val + 1
  omega

/-- SNOVA's attempted counter bytes contain no duplicates. -/
theorem nodup_signingAttemptCounters : signingAttemptCounters.Nodup :=
  pairwise_lt_signingAttemptCounters.imp Fin.ne_of_lt

/-- The first attempted counter byte is `1`. -/
theorem first_signingAttemptCounter :
    signingAttemptCounters[0]'(by simp) = (1 : Fin 256) := by
  apply Fin.ext
  exact getElem_signingAttemptCounters 0 (by simp)

/-- The last attempted counter byte is `254`. -/
theorem last_signingAttemptCounter :
    signingAttemptCounters[253]'(by simp) = (254 : Fin 256) := by
  apply Fin.ext
  exact getElem_signingAttemptCounters 253 (by simp)

end Cslib.Crypto.SNOVA
