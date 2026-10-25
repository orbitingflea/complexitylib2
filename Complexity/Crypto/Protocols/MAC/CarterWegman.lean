/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Computational.PseudorandomFunction
public import Complexity.Languages.Probabilistic.Simulation
public import Complexity.Probability.BitString.LinearHash
public import Complexity.Probability.BitString.SubsetSum
public import Complexity.Probability.HashFamily
public import Complexity.Probability.HashFamily.Polynomial
public import Complexity.Probability.PairwiseIndependentHash.Universal
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Length
import Complexity.Computability.Probabilistic.Oracle.Composition
import Complexity.Crypto.Negligible.Basic
import Complexity.Probability.PMF.Bind
import Complexity.Probability.PMF.Uniform
import Complexity.Tactic.PPT
import Complexity.Tactic.PolyTime

/-!
# Carter–Wegman message authentication codes from Δ-universal hashing

Wegman and Carter [WegmanCarter1981] observed that an `ε`-almost-Δ-universal (`ε`-DUF / `ε`-AXU)
hash family `hash : K → M → Y` into a finite additive group `Y`
(`Cslib.Probability.IsDeltaUniversalHash`) yields an unconditional message authentication code when
each hash digest `hash k m` is masked by a uniform one-time pad `r ∈ Y`:

* **Signing (`sign`)**: `sign hash k r m = hash k m + r`.
* **Verification (`verify`)**: `verify hash k r m t = decide (hash k m + r = t)`.

For every fixed hash key `k` and message `m`, left addition by `hash k m` is a bijection on `Y`, so
a uniform pad `r ← PMF.uniformOfFintype Y` makes the tag `t = hash k m + r` uniformly distributed
on `Y` and independent of `k`, with `r = -hash k m + t` (`map_sign_eq_uniform`,
`bind_uniform_sign`). After seeing `(m, t)`, any forgery attempt `(m', t')` with `m' ≠ m`
verifies under `r = -hash k m + t` if and only if

`hash k m' - hash k m = t' - t` (`verify_neg_add_eq_true_iff`).

Since the adversary's view `(m, t)` is independent of `k`, `IsDeltaUniversalHash seed hash ε`
bounds the probability of this difference equation over `k ← seed` by at most `ε`
([BonehShoup2023], Section 7.6, Lemma 7.11 and Theorem 7.12).

This module formalizes:

1. **Algebraic and resampling properties (`sign`, `verify`, `map_sign_eq_uniform`,
   `bind_uniform_sign`)** over any finite additive group `Y`.
2. **Zero-query forgery (`zeroQueryGame`, `zeroQueryGame_apply_true`)**: without a signing query,
   any forgery attempt succeeds with probability at most (and in fact equal to) `1 / |Y|`.
3. **Adaptive one-time EUF-CMA and SUF-CMA security (`OneTimeForger`, `oneTimeGame`,
   `oneTimeStrongGame`, `oneTimeStrongGame_eq_oneTimeGame`, `oneTimeGame_le`,
   `oneTimeStrongGame_le`)**: because each `(k, r, m)` admits a unique valid tag, strong
   unforgeability (`(m', t') ≠ (m, t)`) and ordinary unforgeability (`m' ≠ m`) coincide and are
   bounded by `ε` ([BonehShoup2023], Section 7.6, Lemma 7.11 and Theorem 7.12).
4. **Adaptive multi-query issued-counter / issued-slot Carter–Wegman MAC (`CounterForger`,
   `counterSlotGame`, `counterGame`, `counterStrongGame`, `counterStrongGame_eq_counterSlotGame`,
   `counterSlotGame_le`, `counterGame_le`, `counterStrongGame_le`)**: when each signing query draws
   an independent uniform pad `r_i ← PMF.uniformOfFintype Y` (recorded at counter index `i`), the
   entire adaptive query transcript is independent of the hash key `k`, so any adaptive `OracleComp`
   forger (making any number of queries) targeting an issued counter index `idx < pads.length` has
   forgery probability at most `ε` under issued-slot message freshness (`counterSlotGame`),
   issued-counter global message freshness (`counterGame`), and issued-slot strong pair freshness
   (`counterStrongGame`), with zero degradation in the number of queries [WegmanCarter1981].
   Unissued counter indices (`pads[idx]? = none`) are rejected (`false`), so zero-query success in
   the issued-counter games is `0` (whereas the standalone `zeroQueryGame` has success `1 / |Y|`);
   a fresh-counter experiment that accepts unissued nonces against fresh pads is separate scope.
5. **Arbitrary-pad hybrid decomposition and the one-query, fixed-nonce PRF-pad reduction
   (`maskedOneTimeGame`, `padDistinguisher`, `maskedOneTimeGame_toReal_le`,
   `maskedOneTimeGame_toReal_le_add_advantage`, `prfPadDist`, `prfOneTimeGame`,
   `prfOneTimeStrongGame`, `prfPadDistinguisher`, `prfOneTimeGame_le`,
   `prfOneTimeStrongGame_le`, `prfOneTimeGame_ofProbComp_le`, `isOraclePPT_prfPadDistinguisher`,
   `wordProbPadTest`, `isPPTOn_wordProbPadTest`,
   `isOraclePPT_prfPadDistinguisher_wordProbPadTest`,
   `PseudorandomFunction.negligible_prfOneTimeGame`,
   `PseudorandomFunction.negligible_prfOneTimeStrongGame`,
   `PseudorandomFunction.negligible_prfOneTimeGame_wordProbPadTest`,
   `PseudorandomFunction.negligible_prfOneTimeStrongGame_wordProbPadTest`)**: replacing the uniform
   pad `r ← PMF.uniformOfFintype Y` with any pad distribution `padDist : PMF Y` bounds the real
   forgery probability by `ε.toReal` plus the distinguishing advantage of `padDistinguisher` between
   `padDist` and `PMF.uniformOfFintype Y` (after [BonehShoup2023], Section 7.4). In the one-query,
   fixed-nonce case where `Y = BitString n` and the pad is generated by evaluating `family` at the
   fixed nonce `List.replicate n false` under a uniform `n`-bit key (`prfPadDist family n`), the
   single-query `OracleDistinguisher` adapter `prfPadDistinguisher` realizes the real and ideal pad
   experiments inside `prfRealGame` and `prfIdealGame` at each parameter `n`, is uniformly strict
   oracle-PPT (`IsOraclePPT encBool`) whenever the pad test is uniformly strict PPT, and yields
   negligible forgery probability under `PseudorandomFunction family` and `Negligible ε`.
6. **Multi-query fresh-nonce PRF-masked Carter–Wegman MAC (`counterSeqHandler`,
   `maskedCounterSlotGame`, `maskedCounterGame`, `maskedCounterStrongGame`,
   `counterPadSeqDistinguisher`, `prfPadSeqDist`, `prfCounterSlotGame`, `prfCounterGame`,
   `prfCounterStrongGame`, `prfMultiPadDistinguisher`, `prfCounterSlotGame_le`,
   `prfCounterGame_le`, `prfCounterStrongGame_le`, `isOraclePPT_prfMultiPadDistinguisher`,
   `PseudorandomFunction.negligible_prfCounterSlotGame`,
   `PseudorandomFunction.negligible_prfCounterGame`,
   `PseudorandomFunction.negligible_prfCounterStrongGame`)**: when the `i`-th signing query uses a
   PRF pad `BitString.ofList n (prfOracle family n key (nonce n i))` at pairwise distinct `n`-bit
   nonces `nonce n 0, ..., nonce n (Q n - 1)`, any `Q n`-query-bounded adaptive `CounterForger` has
   forgery probability at most `ε.toReal` plus the concrete `Q n`-query PRF distinguishing advantage
   of `prfMultiPadDistinguisher Q nonce test`, and negligible forgery probability when `family` is a
   `PseudorandomFunction` and `ε` is `Negligible` (after [BonehShoup2023], Section 7.5,
   Theorem 7.10). This models the nonce-based Carter–Wegman construction under two restrictions
   compared to Boneh–Shoup Attack Game 7.4: (a) the signer's counter schedule `nonce n i` fixes the
   nonces rather than letting the adversary choose distinct nonces, and (b) `checkCounterSlot` /
   `checkCounterGlobal` / `checkCounterStrong` accept forgeries only at issued counter slots
   (`pads[idx]? = some r`) and reject unissued `idx`, which removes the `1 / |T|` unissued-nonce
   guessing term.
7. **Concrete instantiations** for Carter–Wegman polynomial hashing (`xpolyHash`, bound
   `(ℓ + 1) / |F|`), Boolean-matrix linear hashing (`BitString.LinearHash.hash`, bound `2⁻ᵐ`),
   subset-sum hashing (`BitString.SubsetSum.hash`, bound `1 / |G|`), and pairwise independent
   hash families (`IsPairwiseIndependentHash`, bound `1 / |Y|`).

## Main definitions

* `Cslib.Crypto.Protocols.CarterWegman.sign`, `Cslib.Crypto.Protocols.CarterWegman.verify`:
  Carter–Wegman tag generation and verification.
* `Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame`: zero-query forgery experiment.
* `Cslib.Crypto.Protocols.CarterWegman.OneTimeForger`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame`: adaptive one-time EUF-CMA and SUF-CMA
  experiments.
* `Cslib.Crypto.Protocols.CarterWegman.CounterForger`,
  `Cslib.Crypto.Protocols.CarterWegman.counterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame`: adaptive multi-query issued-counter
  Carter–Wegman experiments.
* `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.padDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.probPadTest`,
  `Cslib.Crypto.Protocols.CarterWegman.wordProbPadTest`: arbitrary-pad one-time Carter–Wegman
  experiment and its induced `PMF` and `ProbComp` pad distinguishers.
* `Cslib.Crypto.Protocols.CarterWegman.prfPadDist`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfPadDistinguisher`: one-query, fixed-nonce PRF-masked
  Carter–Wegman experiments and the single-query `OracleDistinguisher` adapter.
* `Cslib.Crypto.Protocols.CarterWegman.counterSeqHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedCounterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedCounterGame`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedCounterStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterPadSeqDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.prfPadSeqDist`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.prfMultiPadDistinguisher`: multi-query fresh-nonce
  PRF-masked Carter–Wegman experiments and the `Q`-query `OracleDistinguisher` adapter.

## Main results

* `Cslib.Crypto.Protocols.CarterWegman.zeroQueryGame_apply_true`: exact `1 / |Y|` zero-query
  forgery probability.
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_eq_oneTimeGame`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeStrongGame_le`: Boneh–Shoup Section 7.6, Lemma 7.11
  and Theorem 7.12 (`≤ ε`).
* `Cslib.Crypto.Protocols.CarterWegman.run_interpret_counterRealHandler`: simulation equivalence
  between real and simulated signing handlers under transcript mapping.
* `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_eq_counterSlotGame`,
  `Cslib.Crypto.Protocols.CarterWegman.counterSlotGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterStrongGame_le`: multi-query issued-counter
  Carter–Wegman security (`≤ ε`).
* `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedOneTimeGame_toReal_le_add_advantage`: arbitrary-pad
  hybrid bounds.
* `Cslib.Crypto.Protocols.CarterWegman.eval_prfRealGame_prfPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfIdealGame_prfPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeStrongGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame_ofProbComp_le`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.isPPTOn_wordProbPadTest`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfPadDistinguisher_wordProbPadTest`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeGame`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeStrongGame`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeGame_wordProbPadTest`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeStrongGame_wordProbPadTest`: single-query
  PRF-pad reduction, `IsOraclePPT` admissibility, and asymptotic security (after Boneh–Shoup
  Section 7.4).
* `Cslib.Crypto.Protocols.CarterWegman.uniform_bind_run_interpret_counterSeqHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfRealGame_prfMultiPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfIdealGame_prfMultiPadDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterSlotGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfCounterStrongGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfMultiPadDistinguisher`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfCounterSlotGame`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfCounterGame`,
  `Cslib.Crypto.PseudorandomFunction.negligible_prfCounterStrongGame`: multi-query fresh-nonce
  PRF-masked Carter–Wegman security, `IsOraclePPT` admissibility, and asymptotic security
  (after Boneh–Shoup Section 7.5, Theorem 7.10).
* `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_xpolyHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.prfOneTimeGame_linearHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_subsetSum_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_subsetSum_le`,
  `Cslib.Crypto.Protocols.CarterWegman.oneTimeGame_of_isPairwiseIndependentHash_le`,
  `Cslib.Crypto.Protocols.CarterWegman.counterGame_of_isPairwiseIndependentHash_le`.

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 7.4–7.6.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.CarterWegman

open Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped NNReal ENNReal

/-! ### Core Carter–Wegman signing, verification, and pad resampling -/

section Core

variable {K M Y : Type*} [AddGroup Y]

/-- Carter–Wegman tag generation ([WegmanCarter1981]; [BonehShoup2023], Section 7.4):
mask the hash digest `hash k m` by adding the pad `r`. -/
def sign (hash : K → M → Y) (k : K) (r : Y) (m : M) : Y :=
  hash k m + r

/-- Carter–Wegman tag verification: check whether `hash k m + r = t`. -/
def verify [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) : Bool :=
  decide (hash k m + r = t)

@[simp]
theorem verify_eq_true_iff [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) :
    verify hash k r m t = true ↔ hash k m + r = t :=
  decide_eq_true_iff

@[simp]
theorem verify_sign [DecidableEq Y] (hash : K → M → Y) (k : K) (r : Y) (m : M) :
    verify hash k r m (sign hash k r m) = true := by
  simp [sign, verify]

/-- Every valid tag for `(k, r, m)` equals `sign hash k r m`. -/
theorem eq_sign_of_verify_eq_true [DecidableEq Y] {hash : K → M → Y} {k : K} {r : Y} {m : M}
    {t : Y} (h : verify hash k r m t = true) :
    t = sign hash k r m :=
  ((verify_eq_true_iff hash k r m t).mp h).symm

/-- Solving for the pad `r` from a message–tag pair `(m, t)`:
`sign hash k r m = t ↔ r = -hash k m + t`. -/
theorem sign_eq_iff_eq_neg_add (hash : K → M → Y) (k : K) (r : Y) (m : M) (t : Y) :
    sign hash k r m = t ↔ r = -hash k m + t :=
  ⟨fun h => by rw [← h, sign, neg_add_cancel_left],
    fun h => by rw [h, sign, add_neg_cancel_left]⟩

/-- After observing tag `t = hash k m + r` (so `r = -hash k m + t`), a candidate pair `(m', t')`
verifies if and only if `hash k m' - hash k m = t' - t`. -/
theorem verify_neg_add_eq_true_iff [DecidableEq Y] (hash : K → M → Y) (k : K) (m m' : M)
    (t t' : Y) :
    verify hash k (-hash k m + t) m' t' = true ↔ hash k m' - hash k m = t' - t := by
  rw [verify_eq_true_iff, ← add_assoc, ← sub_eq_add_neg, eq_sub_iff_add_eq.symm]

/-- Boolean form of `verify_neg_add_eq_true_iff`. -/
theorem verify_neg_add_decide [DecidableEq Y] (hash : K → M → Y) (k : K) (m m' : M)
    (t t' : Y) :
    verify hash k (-hash k m + t) m' t' = decide (hash k m' - hash k m = t' - t) :=
  Bool.eq_iff_iff.mpr (by rw [verify_neg_add_eq_true_iff, decide_eq_true_iff])

/-- Because `(k, r, m)` determines a unique valid tag `sign hash k r m`, pair freshness
`(m', t') ≠ (m, sign hash k r m)` and message freshness `m' ≠ m` agree on all verifying pairs. -/
theorem decide_ne_pair_and_verify_eq [DecidableEq M] [DecidableEq Y]
    (hash : K → M → Y) (k : K) (r : Y) (m : M) (p : M × Y) :
    (decide (p ≠ (m, sign hash k r m)) && verify hash k r p.1 p.2) =
      (decide (p.1 ≠ m) && verify hash k r p.1 p.2) := by
  rcases p with ⟨m', t'⟩
  by_cases hv : verify hash k r m' t' = true
  · have ht : t' = sign hash k r m' := eq_sign_of_verify_eq_true hv
    subst ht
    by_cases hm : m' = m <;> simp [hm, hv]
  · simp [Bool.eq_false_iff.mpr hv]

/-- For a uniform pad `r ← PMF.uniformOfFintype Y`, the tag `sign hash k r m` is uniformly
distributed on `Y` for every `k` and `m`. -/
theorem map_sign_eq_uniform [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M) :
    (PMF.uniformOfFintype Y).map (sign hash k · m) = PMF.uniformOfFintype Y :=
  PMF.uniformOfFintype_map_equiv (Equiv.addLeft (hash k m))

/-- **Pad-to-tag change of variables**: sampling a uniform pad `r ← PMF.uniformOfFintype Y` and
passing `(sign hash k r m, r)` to a continuation `f` is identical to sampling a uniform tag
`t ← PMF.uniformOfFintype Y` and reconstructing `r = -hash k m + t`. -/
theorem bind_uniform_sign {α : Type*} [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M)
    (f : Y → Y → PMF α) :
    ((PMF.uniformOfFintype Y).bind fun r => f (sign hash k r m) r) =
      (PMF.uniformOfFintype Y).bind fun t => f t (-hash k m + t) := by
  conv_rhs => rw [← PMF.uniformOfFintype_map_equiv (Equiv.addLeft (hash k m))]
  rw [PMF.bind_map]
  congr 1
  funext r
  simp [sign, neg_add_cancel_left]

/-- Under `IsDeltaUniversalHash seed hash ε`, for any fixed `(m, t)` and candidate `(m', t')`,
the probability over `k ← seed` that `m' ≠ m` and `(m', t')` verifies against the reconstructed
pad `-hash k m + t` is at most `ε`. -/
private theorem seed_bind_verify_neg_add_le [DecidableEq M] [DecidableEq Y]
    {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (m m' : M) (t t' : Y) :
    (seed.bind fun k =>
      PMF.pure (decide (m' ≠ m) && verify hash k (-hash k m + t) m' t')) true ≤ ε := by
  by_cases hm : m' = m
  · simp [hm]
  · have h_eq : (seed.bind fun k =>
        PMF.pure (decide (m' ≠ m) && verify hash k (-hash k m + t) m' t')) true =
        seed.toOuterMeasure {k | hash k m' - hash k m = t' - t} := by
      rw [PMF.bind_apply, PMF.toOuterMeasure_apply]
      refine tsum_congr fun k => ?_
      rw [decide_eq_true hm, Bool.true_and, verify_neg_add_decide]
      by_cases hk : hash k m' - hash k m = t' - t <;> simp [hk]
    rw [h_eq]
    exact hh m' m hm (t' - t)

end Core

/-! ### Zero-query forgery experiment -/

section ZeroQuery

variable {K M Y : Type} [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq Y]

/-- The zero-query forgery experiment: sample `k ← seed`, `r ← PMF.uniformOfFintype Y`, and
`(m', t') ← forger`, and check whether `verify hash k r m' t' = true`. -/
noncomputable def zeroQueryGame (seed : PMF K) (hash : K → M → Y) (forger : PMF (M × Y)) :
    PMF Bool := do
  let k ← seed
  let r ← PMF.uniformOfFintype Y
  let p ← forger
  return verify hash k r p.1 p.2

/-- Without any signing query, every forgery distribution `forger : PMF (M × Y)` succeeds with
probability **exactly** `1 / |Y|`, regardless of the hash family `hash` or key distribution
`seed`. -/
theorem zeroQueryGame_apply_true (seed : PMF K) (hash : K → M → Y) (forger : PMF (M × Y)) :
    zeroQueryGame seed hash forger true = (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  dsimp only [zeroQueryGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine bind_apply_of_forall seed fun k => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype Y) forger]
  refine bind_apply_of_forall forger fun ⟨m', t'⟩ => ?_
  have h1 : ((PMF.uniformOfFintype Y).bind fun r => PMF.pure (verify hash k r m' t')) =
      (PMF.uniformOfFintype Y).map (fun t => decide (t = t')) := by
    conv_rhs => rw [← map_sign_eq_uniform hash k m']
    rw [PMF.map_comp]
    rfl
  rw [h1, PMF.map_apply, tsum_eq_single t']
  · simp [PMF.uniformOfFintype_apply]
  · intro t ht
    simp [ht]

end ZeroQuery

/-! ### Adaptive one-time Carter–Wegman EUF-CMA and SUF-CMA (Boneh–Shoup Section 7.6) -/

section OneTime

variable {K M Y : Type} [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y]

/-- An adaptive one-time forger against a Carter–Wegman MAC:
it chooses a signing query `m ← query`, receives its tag `t = sign hash k r m`, and outputs a
candidate forgery `(m', t') ← forge m t`. -/
structure OneTimeForger (M Y : Type) where
  /-- Distribution of the single signing query `m`. -/
  query : PMF M
  /-- Forgery distribution given the queried message `m` and its tag `t`. -/
  forge : M → Y → PMF (M × Y)

/-- The adaptive one-time EUF-CMA experiment ([BonehShoup2023], Section 7.6, Lemma 7.11 and
Theorem 7.12): the forger wins if `m' ≠ m` and `verify hash k r m' t' = true`. -/
noncomputable def oneTimeGame (seed : PMF K) (hash : K → M → Y) (forger : OneTimeForger M Y) :
    PMF Bool := do
  let k ← seed
  let r ← PMF.uniformOfFintype Y
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- The adaptive one-time SUF-CMA (strong unforgeability) experiment:
the forger wins if `(m', t') ≠ (m, sign hash k r m)` and `verify hash k r m' t' = true`. -/
noncomputable def oneTimeStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool := do
  let k ← seed
  let r ← PMF.uniformOfFintype Y
  let m ← forger.query
  let t := sign hash k r m
  let p ← forger.forge m t
  return (decide (p ≠ (m, t)) && verify hash k r p.1 p.2)

/-- Strong unforgeability and ordinary unforgeability coincide for the one-time Carter–Wegman MAC,
because each `(k, r, m)` admits a unique valid tag. -/
theorem oneTimeStrongGame_eq_oneTimeGame (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    oneTimeStrongGame seed hash forger = oneTimeGame seed hash forger := by
  dsimp only [oneTimeStrongGame, oneTimeGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1; funext k; congr 1; funext r; congr 1; funext m; congr 1; funext p
  rw [decide_ne_pair_and_verify_eq]

/-- Reformulation of `oneTimeGame` via `bind_uniform_sign`: the queried message `m`, uniform tag
`t`, and candidate forgery `p = (m', t')` are sampled independently of the hash key `k`, which is
drawn last to test `verify hash k (-hash k m + t) m' t'`. -/
theorem oneTimeGame_eq_bind_uniform (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    oneTimeGame seed hash forger =
      forger.query.bind fun m =>
        (PMF.uniformOfFintype Y).bind fun t =>
          (forger.forge m t).bind fun p =>
            seed.bind fun k =>
              PMF.pure (decide (p.1 ≠ m) && verify hash k (-hash k m + t) p.1 p.2) := by
  dsimp only [oneTimeGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have h1 (k : K) :
      ((PMF.uniformOfFintype Y).bind fun r =>
        forger.query.bind fun m =>
          (forger.forge m (sign hash k r m)).bind fun p =>
            PMF.pure (decide (p.1 ≠ m) && verify hash k r p.1 p.2)) =
      (forger.query.bind fun m =>
        (PMF.uniformOfFintype Y).bind fun t =>
          (forger.forge m t).bind fun p =>
            PMF.pure (decide (p.1 ≠ m) && verify hash k (-hash k m + t) p.1 p.2)) := by
    rw [PMF.bind_comm (PMF.uniformOfFintype Y) forger.query]
    congr 1
    funext m
    exact bind_uniform_sign hash k m fun t r =>
      (forger.forge m t).bind fun p =>
        PMF.pure (decide (p.1 ≠ m) && verify hash k r p.1 p.2)
  simp only [h1]
  rw [PMF.bind_comm seed forger.query]
  congr 1; funext m
  rw [PMF.bind_comm seed (PMF.uniformOfFintype Y)]
  congr 1; funext t
  rw [PMF.bind_comm seed (forger.forge m t)]

/-- **One-time Carter–Wegman EUF-CMA security** ([BonehShoup2023], Section 7.6, Lemma 7.11 and
Theorem 7.12; [WegmanCarter1981]): if `hash` is `ε`-almost-Δ-universal under `seed`
(`IsDeltaUniversalHash seed hash ε`), then every adaptive one-time forger succeeds with
probability at most `ε`. -/
theorem oneTimeGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : OneTimeForger M Y) :
    oneTimeGame seed hash forger true ≤ ε := by
  rw [oneTimeGame_eq_bind_uniform, PMF.bind_apply]
  refine tsum_mul_le_of_forall_le forger.query fun m => ?_
  rw [PMF.bind_apply]
  refine tsum_mul_le_of_forall_le (PMF.uniformOfFintype Y) fun t => ?_
  rw [PMF.bind_apply]
  refine tsum_mul_le_of_forall_le (forger.forge m t) fun p => ?_
  exact seed_bind_verify_neg_add_le hh m p.1 t p.2

/-- **One-time Carter–Wegman SUF-CMA security**: under `IsDeltaUniversalHash seed hash ε`, every
adaptive one-time forger has strong-forgery probability at most `ε`. -/
theorem oneTimeStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : OneTimeForger M Y) :
    oneTimeStrongGame seed hash forger true ≤ ε := by
  rw [oneTimeStrongGame_eq_oneTimeGame]
  exact oneTimeGame_le hh forger

end OneTime

/-! ### Adaptive multi-query issued-counter Carter–Wegman MAC -/

section Counter

variable {K M Y : Type} [AddGroup Y]

/-- An adaptive multi-query forger against an issued-counter Carter–Wegman MAC:
it draws private coins `s ← coins`, makes any number of adaptive signing queries `m : M` via
`OracleComp (fun _ : M => Y)` (receiving `t_i = sign hash k r_i m_i` under a fresh pad `r_i` for
the `i`-th query), and outputs a target issued counter index `idx : ℕ`, message `m' : M`, and tag
`t' : Y`. -/
structure CounterForger (M Y : Type) where
  /-- Type of the forger's private coins. -/
  Coins : Type
  /-- Distribution of the forger's private coins. -/
  coins : PMF Coins
  /-- Adaptive oracle program outputting `(idx, m', t')`. -/
  forge : Coins → OracleComp (fun _ : M => Y) (ℕ × M × Y)

/-- Real counter Carter–Wegman signing handler: on query `m`, sample a fresh pad
`r ← PMF.uniformOfFintype Y`, append `(m, r)` to the pad log, and return `sign hash k r m`. -/
noncomputable def counterRealHandler [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M) :
    StateT (List (M × Y)) PMF Y := fun pads => do
  let r ← PMF.uniformOfFintype Y
  return (sign hash k r m, pads ++ [(m, r)])

/-- Simulated key-independent tag handler: on query `m`, sample a fresh uniform tag
`t ← PMF.uniformOfFintype Y`, append `(m, t)` to the message–tag transcript, and return `t`. -/
noncomputable def counterSimHandler [Fintype Y] [Nonempty Y] (m : M) :
    StateT (List (M × Y)) PMF Y := fun tr => do
  let t ← PMF.uniformOfFintype Y
  return (t, tr ++ [(m, t)])

/-- Reconstruct the pad log `[(m_i, -hash k m_i + t_i)]` from a message–tag transcript
`[(m_i, t_i)]`. -/
def transcriptToPads (hash : K → M → Y) (k : K) (tr : List (M × Y)) : List (M × Y) :=
  tr.map fun p => (p.1, -hash k p.1 + p.2)

/-- Running any adaptive `OracleComp` program against `counterRealHandler hash k` from
`transcriptToPads hash k tr` has the exact distribution of running it against the key-independent
`counterSimHandler` from `tr` and applying `transcriptToPads hash k` to the final transcript. -/
theorem run_interpret_counterRealHandler {α : Type} [Fintype Y] [Nonempty Y] (hash : K → M → Y)
    (k : K) (prog : OracleComp (fun _ : M => Y) α) (tr : List (M × Y)) :
    (OracleComp.interpret (counterRealHandler hash k) prog).run (transcriptToPads hash k tr) =
      ((OracleComp.interpret counterSimHandler prog).run tr).map
        (fun x => (x.1, transcriptToPads hash k x.2)) := by
  refine (OracleComp.run_interpret_map_state counterSimHandler (counterRealHandler hash k)
    (transcriptToPads hash k) (fun m s => ?_) prog tr).symm
  dsimp only [counterSimHandler, counterRealHandler, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, StateT.pure]
  rw [PMF.map_bind]
  symm
  simpa only [PMF.bind_pure, PMF.pure_map, Function.comp_def, transcriptToPads, List.map_append,
    List.map_cons, List.map_nil] using
    bind_uniform_sign hash k m fun t r =>
      PMF.pure (t, transcriptToPads hash k s ++ [(m, r)])

variable [DecidableEq M] [DecidableEq Y]

/-- Issued-slot message-freshness verification predicate on a pad log `pads`: the target counter
`idx` was issued (`pads[idx]? = some (m_idx, r_idx)`, returning `false` on unissued indices),
`m' ≠ m_idx`, and `verify hash k r_idx m' t' = true`. -/
def checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  match pads[out.1]? with
  | none => false
  | some (m_idx, r_idx) => decide (out.2.1 ≠ m_idx) && verify hash k r_idx out.2.1 out.2.2

/-- Issued-counter global-message-freshness EUF-CMA verification predicate on a pad log `pads`:
the target counter `idx` was issued (`pads[idx]? = some (_, r_idx)`, returning `false` on unissued
indices), `m'` was never queried in any issued slot (`!(pads.map Prod.fst).contains m'`), and
`verify hash k r_idx m' t' = true`. -/
def checkCounterEUF (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  match pads[out.1]? with
  | none => false
  | some (_, r_idx) =>
    !(pads.map Prod.fst).contains out.2.1 && verify hash k r_idx out.2.1 out.2.2

/-- Issued-slot strong SUF-CMA verification predicate on a pad log `pads`: the target counter `idx`
was issued (`pads[idx]? = some (m_idx, r_idx)`, returning `false` on unissued indices), the pair
`(m', t')` differs from the pair `(m_idx, sign hash k r_idx m_idx)` issued at counter `idx`, and
`verify hash k r_idx m' t' = true`. -/
def checkCounterSUF (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) : Bool :=
  match pads[out.1]? with
  | none => false
  | some (m_idx, r_idx) =>
    decide ((out.2.1, out.2.2) ≠ (m_idx, sign hash k r_idx m_idx)) &&
      verify hash k r_idx out.2.1 out.2.2

/-- Issued-slot SUF-CMA and issued-slot EUF-CMA checks are identical on every pad log and
output. -/
theorem checkCounterSUF_eq_checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) :
    checkCounterSUF hash k pads out = checkCounterSlot hash k pads out := by
  dsimp only [checkCounterSUF, checkCounterSlot]
  cases pads[out.1]? with
  | none => rfl
  | some p => exact decide_ne_pair_and_verify_eq hash k p.2 p.1 out.2

/-- Issued-counter global message freshness implies issued-slot message freshness at the target
counter `idx`. -/
theorem checkCounterEUF_imp_checkCounterSlot (hash : K → M → Y) (k : K) (pads : List (M × Y))
    (out : ℕ × M × Y) :
    checkCounterEUF hash k pads out = true → checkCounterSlot hash k pads out = true := by
  dsimp only [checkCounterEUF, checkCounterSlot]
  cases hget : pads[out.1]? with
  | none => simp
  | some p =>
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
      List.mem_map, decide_eq_true_iff]
    rintro ⟨hnotmem, hv⟩
    refine ⟨fun heq => hnotmem ⟨p, List.mem_of_getElem? hget, heq.symm⟩, hv⟩

variable [Fintype Y] [Nonempty Y]

/-- The issued-slot EUF-CMA experiment for the counter Carter–Wegman MAC (unissued indices `idx`
are rejected). -/
noncomputable def counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterSlot hash k res.2 res.1

/-- The issued-counter global-message-freshness EUF-CMA experiment for the counter Carter–Wegman
MAC (unissued indices `idx` are rejected). -/
noncomputable def counterGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterEUF hash k res.2 res.1

/-- The issued-slot strong SUF-CMA experiment for the counter Carter–Wegman MAC (unissued indices
`idx` are rejected). -/
noncomputable def counterStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []
  return checkCounterSUF hash k res.2 res.1

/-- Issued-slot strong unforgeability (`counterStrongGame`) and issued-slot EUF-CMA
(`counterSlotGame`) have identical outcome distributions. -/
theorem counterStrongGame_eq_counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) :
    counterStrongGame seed hash forger = counterSlotGame seed hash forger := by
  dsimp only [counterStrongGame, counterSlotGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1; funext k; congr 1; funext s; congr 1; funext res
  rw [checkCounterSUF_eq_checkCounterSlot]

/-- Issued-counter global-message-freshness EUF-CMA success probability is at most issued-slot
EUF-CMA success probability. -/
theorem counterGame_le_counterSlotGame (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) :
    counterGame seed hash forger true ≤ counterSlotGame seed hash forger true := by
  dsimp only [counterGame, counterSlotGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine bind_apply_mono_on_support seed true fun k _ => ?_
  refine bind_apply_mono_on_support forger.coins true fun s _ => ?_
  refine bind_apply_mono_on_support
    ((OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []) true fun res _ =>
      ?_
  by_cases h : checkCounterEUF hash k res.2 res.1 = true
  · rw [h, checkCounterEUF_imp_checkCounterSlot hash k res.2 res.1 h]
  · simp [Bool.eq_false_iff.mpr h]

/-- **Multi-query issued-slot Carter–Wegman security** ([WegmanCarter1981];
[BonehShoup2023], Section 7.4): under `IsDeltaUniversalHash seed hash ε`, every adaptive
multi-query forger succeeds in `counterSlotGame` with probability at most `ε`, with zero
degradation in the number of signing queries. -/
theorem counterSlotGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterSlotGame seed hash forger true ≤ ε := by
  dsimp only [counterSlotGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  have hrun (k : K) (s : forger.Coins) :
      (((OracleComp.interpret (counterRealHandler hash k) (forger.forge s)).run []).bind fun res =>
        PMF.pure (checkCounterSlot hash k res.2 res.1)) =
      (((OracleComp.interpret counterSimHandler (forger.forge s)).run []).bind fun res =>
        PMF.pure (checkCounterSlot hash k (transcriptToPads hash k res.2) res.1)) := by
    have h := run_interpret_counterRealHandler hash k (forger.forge s) []
    simp only [transcriptToPads, List.map_nil] at h
    rw [h, PMF.bind_map]
    rfl
  simp only [hrun]
  rw [PMF.bind_comm seed forger.coins]
  rw [PMF.bind_apply]
  refine tsum_mul_le_of_forall_le forger.coins fun s => ?_
  rw [PMF.bind_comm seed ((OracleComp.interpret counterSimHandler (forger.forge s)).run [])]
  rw [PMF.bind_apply]
  refine tsum_mul_le_of_forall_le ((OracleComp.interpret counterSimHandler (forger.forge s)).run [])
    fun ⟨⟨idx, m', t'⟩, tr⟩ => ?_
  dsimp only [checkCounterSlot, transcriptToPads]
  simp only [List.getElem?_map]
  cases tr[idx]? with
  | none => simp
  | some p =>
    exact seed_bind_verify_neg_add_le hh p.1 m' p.2 t'

/-- **Multi-query issued-counter Carter–Wegman EUF-CMA security**: under
`IsDeltaUniversalHash seed hash ε`, every adaptive multi-query forger has issued-counter EUF-CMA
forgery probability at most `ε`. -/
theorem counterGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterGame seed hash forger true ≤ ε :=
  (counterGame_le_counterSlotGame seed hash forger).trans (counterSlotGame_le hh forger)

/-- **Multi-query issued-slot Carter–Wegman SUF-CMA security**: under
`IsDeltaUniversalHash seed hash ε`, every adaptive multi-query forger has issued-slot SUF-CMA
forgery probability at most `ε`. -/
theorem counterStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (forger : CounterForger M Y) :
    counterStrongGame seed hash forger true ≤ ε := by
  rw [counterStrongGame_eq_counterSlotGame]
  exact counterSlotGame_le hh forger

end Counter

/-! ### Pseudorandom-pad hybrid decomposition (after Boneh–Shoup Section 7.4) -/

section MaskedPad

variable {K M Y : Type} [AddGroup Y] [DecidableEq M] [DecidableEq Y]

/-- The one-time Carter–Wegman experiment with an arbitrary pad distribution `padDist : PMF Y`
(such as a pseudorandom function output `F(k₂, nonce)`). -/
noncomputable def maskedOneTimeGame (seed : PMF K) (padDist : PMF Y) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool := do
  let k ← seed
  let r ← padDist
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- The strong one-time Carter–Wegman experiment with an arbitrary pad distribution
`padDist : PMF Y`. -/
noncomputable def maskedOneTimeStrongGame (seed : PMF K) (padDist : PMF Y) (hash : K → M → Y)
    (forger : OneTimeForger M Y) : PMF Bool := do
  let k ← seed
  let r ← padDist
  let m ← forger.query
  let t := sign hash k r m
  let p ← forger.forge m t
  return (decide (p ≠ (m, t)) && verify hash k r p.1 p.2)

@[simp]
theorem maskedOneTimeGame_uniform [Fintype Y] [Nonempty Y] (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) :
    maskedOneTimeGame seed (PMF.uniformOfFintype Y) hash forger =
      oneTimeGame seed hash forger :=
  rfl

theorem maskedOneTimeStrongGame_eq_maskedOneTimeGame (seed : PMF K) (padDist : PMF Y)
    (hash : K → M → Y) (forger : OneTimeForger M Y) :
    maskedOneTimeStrongGame seed padDist hash forger =
      maskedOneTimeGame seed padDist hash forger := by
  dsimp only [maskedOneTimeStrongGame, maskedOneTimeGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  congr 1; funext k; congr 1; funext r; congr 1; funext m; congr 1; funext p
  rw [decide_ne_pair_and_verify_eq]

/-- The induced pad distinguisher `Y → PMF Bool` that samples `k ← seed`, simulates the one-time
Carter–Wegman experiment using the supplied pad `r : Y`, and outputs `true` iff the forger
produces a valid forgery. -/
noncomputable def padDistinguisher (seed : PMF K) (hash : K → M → Y)
    (forger : OneTimeForger M Y) (r : Y) : PMF Bool := do
  let k ← seed
  let m ← forger.query
  let p ← forger.forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

/-- `maskedOneTimeGame` is equivalent to sampling `r ← padDist` and running
`padDistinguisher seed hash forger r`. -/
theorem maskedOneTimeGame_eq_bind_padDistinguisher (seed : PMF K) (padDist : PMF Y)
    (hash : K → M → Y) (forger : OneTimeForger M Y) :
    maskedOneTimeGame seed padDist hash forger =
      padDist.bind (padDistinguisher seed hash forger) :=
  PMF.bind_comm seed padDist _

/-- **Pseudorandom-pad Carter–Wegman bound** (after [BonehShoup2023], Section 7.4):
if `hash` is `ε`-almost-Δ-universal (`ε ≠ ⊤`), then the real-valued forgery probability under any
pad distribution `padDist : PMF Y` is bounded by `ε.toReal` plus the distinguishing gap of
`padDistinguisher` between `padDist` and `PMF.uniformOfFintype Y`. -/
theorem maskedOneTimeGame_toReal_le [Fintype Y] [Nonempty Y] {seed : PMF K} {hash : K → M → Y}
    {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤) (padDist : PMF Y)
    (forger : OneTimeForger M Y) :
    (maskedOneTimeGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        |((padDist.bind (padDistinguisher seed hash forger)) true).toReal -
          (((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) true).toReal| := by
  have hunif : (PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger) =
      oneTimeGame seed hash forger :=
    (maskedOneTimeGame_eq_bind_padDistinguisher seed (PMF.uniformOfFintype Y) hash forger).symm
  have hle : (oneTimeGame seed hash forger true).toReal ≤ ε.toReal :=
    ENNReal.toReal_mono hε (oneTimeGame_le hh forger)
  rw [maskedOneTimeGame_eq_bind_padDistinguisher, hunif]
  linarith [le_abs_self (((padDist.bind (padDistinguisher seed hash forger)) true).toReal -
    (oneTimeGame seed hash forger true).toReal)]

/-- `Game.advantage` form of `maskedOneTimeGame_toReal_le` (after [BonehShoup2023], Section 7.4):
the real-valued forgery probability under `padDist` is bounded by `ε.toReal` plus
`Game.advantage` between `padDist.bind (padDistinguisher seed hash forger)` and
`(PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)`. -/
theorem maskedOneTimeGame_toReal_le_add_advantage [Fintype Y] [Nonempty Y] {seed : PMF K}
    {hash : K → M → Y} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (padDist : PMF Y) (forger : OneTimeForger M Y) :
    (maskedOneTimeGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage (padDist.bind (padDistinguisher seed hash forger))
          ((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) : ℝ) := by
  rw [Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  exact maskedOneTimeGame_toReal_le hh hε padDist forger

/-- Strong-unforgeability version of `maskedOneTimeGame_toReal_le_add_advantage`. -/
theorem maskedOneTimeStrongGame_toReal_le_add_advantage [Fintype Y] [Nonempty Y] {seed : PMF K}
    {hash : K → M → Y} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (padDist : PMF Y) (forger : OneTimeForger M Y) :
    (maskedOneTimeStrongGame seed padDist hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage (padDist.bind (padDistinguisher seed hash forger))
          ((PMF.uniformOfFintype Y).bind (padDistinguisher seed hash forger)) : ℝ) := by
  rw [maskedOneTimeStrongGame_eq_maskedOneTimeGame]
  exact maskedOneTimeGame_toReal_le_add_advantage hh hε padDist forger

/-- Construct a `OneTimeForger` from `ProbComp` query and forgery programs. -/
noncomputable def OneTimeForger.ofProbComp (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) : OneTimeForger M Y where
  query := ProbComp.eval query
  forge m t := ProbComp.eval (forge m t)

/-- Executable `ProbComp` simulation of the one-time Carter–Wegman experiment with a supplied pad
`r : Y`, given `ProbComp` samplers for the hash key `seed`, signing query `query`, and forgery
attempt `forge`. -/
def probPadTest (seed : ProbComp K) (hash : K → M → Y) (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) (r : Y) : ProbComp Bool := do
  let k ← seed
  let m ← query
  let p ← forge m (sign hash k r m)
  return (decide (p.1 ≠ m) && verify hash k r p.1 p.2)

@[simp]
theorem eval_probPadTest (seed : ProbComp K) (hash : K → M → Y) (query : ProbComp M)
    (forge : M → Y → ProbComp (M × Y)) (r : Y) :
    ProbComp.eval (probPadTest seed hash query forge r) =
      padDistinguisher (ProbComp.eval seed) hash (OneTimeForger.ofProbComp query forge) r := by
  simp [probPadTest, padDistinguisher, OneTimeForger.ofProbComp, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.map, Function.comp_def]

end MaskedPad

/-! ### One-query, fixed-nonce PRF-pad reduction (after Boneh–Shoup Section 7.4) -/

section PRFPad

variable {K M : Type} [DecidableEq M]

/-- The one-time pad distribution on `BitString n` obtained by sampling a uniform `n`-bit PRF key
`key ← BitString.uniformList n` and evaluating `family key (List.replicate n false)`. -/
noncomputable def prfPadDist (family : List Bool → List Bool → List Bool) (n : ℕ) :
    PMF (BitString n) :=
  (BitString.uniformList n).map fun key =>
    BitString.ofList n (family key (List.replicate n false))

/-- The one-query, fixed-nonce PRF-masked Carter–Wegman EUF-CMA experiment (after
[BonehShoup2023], Section 7.4): the pad `r : BitString n` is generated by evaluating `family` on a
uniform `n`-bit PRF key at the fixed nonce `List.replicate n false`. -/
noncomputable def prfOneTimeGame (seed : PMF K) (family : List Bool → List Bool → List Bool)
    (n : ℕ) (hash : K → M → BitString n) (forger : OneTimeForger M (BitString n)) : PMF Bool :=
  maskedOneTimeGame seed (prfPadDist family n) hash forger

/-- The one-query, fixed-nonce PRF-masked Carter–Wegman SUF-CMA experiment (after
[BonehShoup2023], Section 7.4). -/
noncomputable def prfOneTimeStrongGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (hash : K → M → BitString n)
    (forger : OneTimeForger M (BitString n)) : PMF Bool :=
  maskedOneTimeStrongGame seed (prfPadDist family n) hash forger

theorem prfOneTimeStrongGame_eq_prfOneTimeGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (hash : K → M → BitString n)
    (forger : OneTimeForger M (BitString n)) :
    prfOneTimeStrongGame seed family n hash forger =
      prfOneTimeGame seed family n hash forger :=
  maskedOneTimeStrongGame_eq_maskedOneTimeGame seed (prfPadDist family n) hash forger

/-- Single-query PRF `OracleDistinguisher` induced by a family of `ProbComp` pad tests
`test : (k : ℕ) → BitString k → ProbComp Bool`: at security parameter `n`, query the oracle once at
the fixed nonce `List.replicate n false` and run `test n` on the `n`-bit view of the reply. -/
def prfPadDistinguisher (test : (k : ℕ) → BitString k → ProbComp Bool) :
    OracleDistinguisher := fun n _ => do
  let reply ← ProbOracleComp.query ((), List.replicate n false)
  ProbOracleComp.sample (test n (BitString.ofList n reply))

/-- In `prfRealGame`, `prfPadDistinguisher test` evaluates `test n` on a pad drawn from
`prfPadDist family n`. -/
theorem eval_prfRealGame_prfPadDistinguisher (family : List Bool → List Bool → List Bool)
    (test : (k : ℕ) → BitString k → ProbComp Bool) (n : ℕ) :
    ProbComp.eval (prfRealGame family (prfPadDistinguisher test) n) =
      (prfPadDist family n).bind (fun r => ProbComp.eval (test n r)) := by
  simp only [prfRealGame, prfPadDistinguisher, prfPadDist, ProbComp.eval_bind,
    BitString.eval_sampleList, PMF.bind_map, Function.comp_def]
  congr 1
  funext key
  simp [prfOracle, show ProbComp.unifFin = OracleComp.query from rfl]

/-- Evaluating a uniformly random function `table : BitString n → BitString n` at any single point
`x : BitString n` produces the uniform distribution on `BitString n`. -/
private theorem map_eval_uniformOfFintype_fun (n : ℕ) (x : BitString n) :
    (PMF.uniformOfFintype (BitString n → BitString n)).map (fun table => table x) =
      PMF.uniformOfFintype (BitString n) := by
  rw [← PMF.pi_uniformOfFintype, PMF.pi_map_eval]

/-- In `prfIdealGame`, `prfPadDistinguisher test` evaluates `test n` on a uniform pad
`r ← PMF.uniformOfFintype (BitString n)`. -/
theorem eval_prfIdealGame_prfPadDistinguisher (test : (k : ℕ) → BitString k → ProbComp Bool)
    (n : ℕ) :
    ProbComp.eval (prfIdealGame (prfPadDistinguisher test) n) =
      (PMF.uniformOfFintype (BitString n)).bind (fun r => ProbComp.eval (test n r)) := by
  conv_rhs =>
    rw [← map_eval_uniformOfFintype_fun n (BitString.ofList n (List.replicate n false)),
      PMF.bind_map]
  simp only [prfIdealGame, prfPadDistinguisher, ProbComp.eval_bind, ProbComp.eval_uniform,
    Function.comp_def]
  congr 1
  funext table
  simp [randomFunctionOracle, show ProbComp.unifFin = OracleComp.query from rfl]

/-- **Exact single-query PRF-pad reduction for an explicit `OracleDistinguisher`** in the
one-query, fixed-nonce case (after [BonehShoup2023], Section 7.4): if `D` simulates
`padDistinguisher seed hash forger` in both `prfRealGame` and `prfIdealGame` at parameter `n`, then
the real-valued one-time forgery probability is at most `ε.toReal` plus the concrete PRF
distinguishing advantage of `D` at `n`. -/
theorem prfOneTimeGame_le_of_distinguisher {n : ℕ} {seed : PMF K}
    {hash : K → M → BitString n} {ε : ℝ≥0∞} (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool) (forger : OneTimeForger M (BitString n))
    (D : OracleDistinguisher)
    (hreal : ProbComp.eval (prfRealGame family D n) =
      (prfPadDist family n).bind (padDistinguisher seed hash forger))
    (hideal : ProbComp.eval (prfIdealGame D n) =
      (PMF.uniformOfFintype (BitString n)).bind (padDistinguisher seed hash forger)) :
    (prfOneTimeGame seed family n hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family D n))
          (ProbComp.eval (prfIdealGame D n)) : ℝ) := by
  rw [hreal, hideal]
  exact maskedOneTimeGame_toReal_le_add_advantage hh hε (prfPadDist family n) forger

/-- **Exact single-query PRF-pad reduction for `prfOneTimeGame`** in the one-query, fixed-nonce
case (after [BonehShoup2023], Section 7.4): replacing the uniform pad
`r ← PMF.uniformOfFintype (BitString n)` with the fixed-nonce PRF pad `prfPadDist family n` bounds
the real-valued one-time forgery probability at parameter `n` by `ε.toReal` plus the concrete PRF
distinguishing advantage of `prfPadDistinguisher test` between `prfRealGame` and `prfIdealGame`.
Admissibility (`IsOraclePPT encBool`) and the asymptotic corollary from
`PseudorandomFunction family` are not asserted here. -/
theorem prfOneTimeGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (forger : OneTimeForger M (BitString n))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest : ∀ r, padDistinguisher seed hash forger r = ProbComp.eval (test n r)) :
    (prfOneTimeGame seed family n hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfPadDistinguisher test) n))
          (ProbComp.eval (prfIdealGame (prfPadDistinguisher test) n)) : ℝ) := by
  refine prfOneTimeGame_le_of_distinguisher hh hε family forger (prfPadDistinguisher test) ?_ ?_
  · rw [eval_prfRealGame_prfPadDistinguisher]
    congr 1; funext r; exact (htest r).symm
  · rw [eval_prfIdealGame_prfPadDistinguisher]
    congr 1; funext r; exact (htest r).symm

/-- **Exact single-query PRF-pad reduction for `prfOneTimeStrongGame`** in the one-query,
fixed-nonce case (after [BonehShoup2023], Section 7.4); admissibility (`IsOraclePPT encBool`) and
the asymptotic `PseudorandomFunction` corollary are not asserted here. -/
theorem prfOneTimeStrongGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (forger : OneTimeForger M (BitString n))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest : ∀ r, padDistinguisher seed hash forger r = ProbComp.eval (test n r)) :
    (prfOneTimeStrongGame seed family n hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfPadDistinguisher test) n))
          (ProbComp.eval (prfIdealGame (prfPadDistinguisher test) n)) : ℝ) := by
  rw [prfOneTimeStrongGame_eq_prfOneTimeGame]
  exact prfOneTimeGame_le hh hε family forger test htest

/-- **Exact single-query PRF-pad reduction for `ProbComp` samplers and forgers** in the one-query,
fixed-nonce case (after [BonehShoup2023], Section 7.4): at parameter `n`, any `ProbComp` hash-key
sampler `seed`, query program `query`, and forgery program `forge` induce the single-query PRF
distinguisher via `probPadTest`, without asserting `IsOraclePPT encBool` admissibility or an
asymptotic `PseudorandomFunction` corollary. -/
theorem prfOneTimeGame_ofProbComp_le {n : ℕ} {seed : ProbComp K}
    {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval seed) hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (query : ProbComp M) (forge : M → BitString n → ProbComp (M × BitString n)) :
    (prfOneTimeGame (ProbComp.eval seed) family n hash
      (OneTimeForger.ofProbComp query forge) true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n))
          (ProbComp.eval (prfIdealGame
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n)) : ℝ) := by
  refine prfOneTimeGame_le hh hε family (OneTimeForger.ofProbComp query forge) _ fun r => ?_
  simp

/-- Strong-unforgeability version of `prfOneTimeGame_ofProbComp_le`. -/
theorem prfOneTimeStrongGame_ofProbComp_le {n : ℕ} {seed : ProbComp K}
    {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval seed) hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (query : ProbComp M) (forge : M → BitString n → ProbComp (M × BitString n)) :
    (prfOneTimeStrongGame (ProbComp.eval seed) family n hash
      (OneTimeForger.ofProbComp query forge) true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n))
          (ProbComp.eval (prfIdealGame
            (prfPadDistinguisher fun _ r =>
              probPadTest seed hash query forge (BitString.ofList n (List.ofFn r))) n)) : ℝ) := by
  rw [prfOneTimeStrongGame_eq_prfOneTimeGame]
  exact prfOneTimeGame_ofProbComp_le hh hε family query forge

private theorem ofList_take (n : ℕ) (w : List Bool) :
    BitString.ofList n (w.take n) = BitString.ofList n w := by
  funext i
  simp [BitString.ofList, i.isLt]

/-- `prfPadDistinguisher test` is uniformly strict oracle-PPT (`IsOraclePPT encBool`) whenever
running `test n` on the `n`-bit view of a raw pad word is uniformly strict PPT in `(n, word)`. -/
theorem isOraclePPT_prfPadDistinguisher
    {test : (k : ℕ) → BitString k → ProbComp Bool}
    (htest : IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => test p.1 (BitString.ofList p.1 p.2))) :
    IsOraclePPT encBool (prfPadDistinguisher test) := by
  have heq : prfPadDistinguisher test =
      (fun n _ => do
        let reply ← List.take n <$> ProbOracleComp.query ((), List.replicate n false)
        ProbOracleComp.sample (test n (BitString.ofList n reply))) := by
    funext n _
    simp [prfPadDistinguisher, ofList_take]
  rw [heq]
  have hq : IsOraclePPTOn (encPair encUnary encBits) encBits
      (fun p : ℕ × List Bool =>
        List.take p.1 <$> ProbOracleComp.query ((), List.replicate p.1 false)) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  exact (hq.bind_with ((htest.preprocess
    (prepare := fun p : (ℕ × List Bool) × List Bool => (p.1.1, p.2))
    (by polytime)).isOraclePPTOn)).isOraclePPT

/-- Executable `ProbComp` one-time pad test induced by a uniform word-level hash-key sampler `seed`,
hash evaluator `hash`, signing query `query`, and forgery program `forge`: at security parameter `n`
and pad `r : BitString n`, it runs `probPadTest` with digest `BitString.ofList n (hash n k m)` and
candidate tag `BitString.ofList n p.2`. -/
def wordProbPadTest (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (query : ℕ → ProbComp (List Bool))
    (forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool))
    (n : ℕ) (r : BitString n) : ProbComp Bool :=
  probPadTest (seed n) (fun k m => BitString.ofList n (hash n k m)) (query n)
    (fun m t => do
      let p ← forge n m (List.ofFn t)
      return (p.1, BitString.ofList n p.2)) r

@[simp]
theorem eval_wordProbPadTest (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (query : ℕ → ProbComp (List Bool))
    (forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool))
    (n : ℕ) (r : BitString n) :
    ProbComp.eval (wordProbPadTest seed hash query forge n r) =
      padDistinguisher (ProbComp.eval (seed n))
        (fun k m => BitString.ofList n (hash n k m))
        (OneTimeForger.ofProbComp (query n) (fun m t => do
          let p ← forge n m (List.ofFn t)
          return (p.1, BitString.ofList n p.2))) r :=
  eval_probPadTest _ _ _ _ r

/-- If `seed`, `hash`, `query`, and `forge` are uniformly polynomial-time / strict PPT in their
encoded inputs, then `wordProbPadTest` on the `n`-bit view of a raw pad word is uniformly strict
PPT. -/
theorem isPPTOn_wordProbPadTest
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hash p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair encBits encBits) (fun p => forge p.1 p.2.1 p.2.2)) :
    IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool =>
        wordProbPadTest seed hash query forge p.1 (BitString.ofList p.1 p.2)) := by
  have hhash_tidy := hhash.tidy
  have heq : (fun p : ℕ × List Bool =>
      wordProbPadTest seed hash query forge p.1 (BitString.ofList p.1 p.2)) =
      fun p : ℕ × List Bool => do
        let k ← seed p.1
        let m ← query p.1
        let out ← forge p.1 m (BitString.listXor p.1 [hash p.1 k m, p.2])
        return (decide (out.1 ≠ m) &&
          decide (BitString.listXor p.1 [hash p.1 k out.1, p.2] =
            BitString.listRow p.1 0 out.2)) := by
    funext ⟨n, rawPad⟩
    simp only [wordProbPadTest, probPadTest, sign, verify, bind_assoc, pure_bind,
      BitString.listXor_pair, BitString.listRow_zero, List.ofFn_injective.eq_iff]
  rw [heq]
  ppt

/-- `prfPadDistinguisher (wordProbPadTest seed hash query forge)` is uniformly strict oracle-PPT
(`IsOraclePPT encBool`) for any uniform polynomial-time / strict-PPT family `(seed, hash, query,
forge)`. -/
theorem isOraclePPT_prfPadDistinguisher_wordProbPadTest
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hash p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair encBits encBits) (fun p => forge p.1 p.2.1 p.2.2)) :
    IsOraclePPT encBool (prfPadDistinguisher (wordProbPadTest seed hash query forge)) :=
  isOraclePPT_prfPadDistinguisher (isPPTOn_wordProbPadTest hseed hhash hquery hforge)

/-- **Asymptotic one-query fixed-nonce PRF-masked Carter–Wegman EUF-CMA security**
(after [BonehShoup2023], Section 7.4): if `family` is a `PseudorandomFunction`, each
`(seed n, hash n)` is `(ε n)`-almost-Δ-universal with `Negligible ε`, and `test` is a uniformly
strict-PPT pad test realizing `padDistinguisher (seed n) (hash n) (forger n)` at every `n`, then the
one-time forgery probability `Game.succProbability (prfOneTimeGame ...)` is `Negligible`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeGame
    {K M : ℕ → Type} [∀ n, DecidableEq (M n)]
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : (n : ℕ) → PMF (K n)} {hash : (n : ℕ) → K n → M n → BitString n}
    {ε : ℕ → ℝ≥0} (hh : ∀ n, IsDeltaUniversalHash (seed n) (hash n) (ε n))
    (hε : Negligible ε)
    (forger : (n : ℕ) → OneTimeForger (M n) (BitString n))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest_eval : ∀ n r,
      padDistinguisher (seed n) (hash n) (forger n) r = ProbComp.eval (test n r))
    (htest_ppt : IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => test p.1 (BitString.ofList p.1 p.2))) :
    Negligible (fun n =>
      Game.succProbability (prfOneTimeGame (seed n) family n (hash n) (forger n))) := by
  have hdist := hprf.secure (prfPadDistinguisher test)
    (isOraclePPT_prfPadDistinguisher htest_ppt)
  refine negligible_of_le (hε.add hdist) fun n => ?_
  rw [← NNReal.coe_le_coe, Game.coe_succProbability, Pi.add_apply, NNReal.coe_add]
  simpa only [ENNReal.coe_toReal] using
    prfOneTimeGame_le (hh n) ENNReal.coe_ne_top family (forger n) test (htest_eval n)

/-- **Asymptotic one-query fixed-nonce PRF-masked Carter–Wegman SUF-CMA security**
(after [BonehShoup2023], Section 7.4). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeStrongGame
    {K M : ℕ → Type} [∀ n, DecidableEq (M n)]
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : (n : ℕ) → PMF (K n)} {hash : (n : ℕ) → K n → M n → BitString n}
    {ε : ℕ → ℝ≥0} (hh : ∀ n, IsDeltaUniversalHash (seed n) (hash n) (ε n))
    (hε : Negligible ε)
    (forger : (n : ℕ) → OneTimeForger (M n) (BitString n))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest_eval : ∀ n r,
      padDistinguisher (seed n) (hash n) (forger n) r = ProbComp.eval (test n r))
    (htest_ppt : IsPPTOn (encPair encUnary encBits) encBool
      (fun p : ℕ × List Bool => test p.1 (BitString.ofList p.1 p.2))) :
    Negligible (fun n =>
      Game.succProbability (prfOneTimeStrongGame (seed n) family n (hash n) (forger n))) := by
  simp only [prfOneTimeStrongGame_eq_prfOneTimeGame]
  exact hprf.negligible_prfOneTimeGame hh hε forger test htest_eval htest_ppt

/-- **Asymptotic one-query fixed-nonce PRF-masked Carter–Wegman EUF-CMA security for uniform
word-level families** (after [BonehShoup2023], Section 7.4). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeGame_wordProbPadTest
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k m => BitString.ofList n (hash n k m)) (ε n))
    (hε : Negligible ε)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hash p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair encBits encBits) (fun p => forge p.1 p.2.1 p.2.2)) :
    Negligible (fun n =>
      Game.succProbability
        (prfOneTimeGame (ProbComp.eval (seed n)) family n
          (fun k m => BitString.ofList n (hash n k m))
          (OneTimeForger.ofProbComp (query n) fun m t => do
            let p ← forge n m (List.ofFn t)
            return (p.1, BitString.ofList n p.2)))) :=
  hprf.negligible_prfOneTimeGame hh hε _ (wordProbPadTest seed hash query forge)
    (fun n r => (eval_wordProbPadTest seed hash query forge n r).symm)
    (isPPTOn_wordProbPadTest hseed hhash hquery hforge)

/-- **Asymptotic one-query fixed-nonce PRF-masked Carter–Wegman SUF-CMA security for uniform
word-level families** (after [BonehShoup2023], Section 7.4). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfOneTimeStrongGame_wordProbPadTest
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {query : ℕ → ProbComp (List Bool)}
    {forge : ℕ → List Bool → List Bool → ProbComp (List Bool × List Bool)}
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k m => BitString.ofList n (hash n k m)) (ε n))
    (hε : Negligible ε)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hash p.1 p.2.1 p.2.2)
      (encPair encUnary (encPair encBits encBits)) encBits)
    (hquery : IsPPTOn encUnary encBits query)
    (hforge : IsPPTOn (encPair encUnary (encPair encBits encBits))
      (encPair encBits encBits) (fun p => forge p.1 p.2.1 p.2.2)) :
    Negligible (fun n =>
      Game.succProbability
        (prfOneTimeStrongGame (ProbComp.eval (seed n)) family n
          (fun k m => BitString.ofList n (hash n k m))
          (OneTimeForger.ofProbComp (query n) fun m t => do
            let p ← forge n m (List.ofFn t)
            return (p.1, BitString.ofList n p.2)))) := by
  simp only [prfOneTimeStrongGame_eq_prfOneTimeGame]
  exact hprf.negligible_prfOneTimeGame_wordProbPadTest hh hε hseed hhash hquery hforge

end PRFPad

/-! ### Multi-query fresh-nonce PRF-masked Carter–Wegman MAC (after Boneh–Shoup Section 7.5) -/

section PRFCounter

variable {K M Y : Type} [AddGroup Y]

/-- Counter Carter–Wegman signing handler driven by a deterministic pad sequence `padSeq : ℕ → Y`:
on the `i`-th query `m` (`i = pads.length`), it uses the pad `r = padSeq pads.length`, appends
`(m, r)` to the pad log, and returns `sign hash k r m`. -/
noncomputable def counterSeqHandler (hash : K → M → Y) (k : K) (padSeq : ℕ → Y) (m : M) :
    StateT (List (M × Y)) PMF Y := fun pads =>
  let r := padSeq pads.length
  PMF.pure (sign hash k r m, pads ++ [(m, r)])

@[simp]
theorem run_counterSeqHandler (hash : K → M → Y) (k : K) (padSeq : ℕ → Y) (m : M)
    (pads : List (M × Y)) :
    (counterSeqHandler hash k padSeq m).run pads =
      PMF.pure (sign hash k (padSeq pads.length) m, pads ++ [(m, padSeq pads.length)]) := rfl

@[simp]
theorem run_counterRealHandler [Fintype Y] [Nonempty Y] (hash : K → M → Y) (k : K) (m : M)
    (pads : List (M × Y)) :
    (counterRealHandler hash k m).run pads =
      (PMF.uniformOfFintype Y).bind fun r => PMF.pure (sign hash k r m, pads ++ [(m, r)]) := rfl

/-- If `prog` makes at most `Q` queries, then running `prog` against `counterSeqHandler` from `pads`
depends only on the pads `padSeq i` for `i ∈ [pads.length, pads.length + Q)`. -/
theorem run_interpret_counterSeqHandler_congr {α : Type} (hash : K → M → Y) (k : K)
    {padSeq₁ padSeq₂ : ℕ → Y} {prog : OracleComp (fun _ : M => Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (pads : List (M × Y))
    (hpad : ∀ i, pads.length ≤ i → i < pads.length + Q → padSeq₁ i = padSeq₂ i) :
    (OracleComp.interpret (counterSeqHandler hash k padSeq₁) prog).run pads =
      (OracleComp.interpret (counterSeqHandler hash k padSeq₂) prog).run pads := by
  induction hprog generalizing pads with
  | pure a Q => rfl
  | liftBind m cont Q hcont ih =>
    simp only [OracleComp.interpret_bind, OracleComp.interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, run_counterSeqHandler, PMF.pure_bind]
    have h0 : padSeq₁ pads.length = padSeq₂ pads.length :=
      hpad pads.length (le_refl _) (by omega)
    rw [h0]
    exact ih (sign hash k (padSeq₂ pads.length) m) (pads ++ [(m, padSeq₂ pads.length)])
      fun i hlo hhi => by
        simp only [List.length_append, List.length_singleton] at hlo hhi
        exact hpad i (by omega) (by omega)

/-- When `table ← PMF.uniformOfFintype (ι → Y)` is a uniformly random function and `nonce : ℕ → ι`
is injective on `[pads.length, pads.length + Q)`, running any `Q`-query-bounded program `prog`
against `counterSeqHandler hash k (fun i => table (nonce i))` from `pads` has the exact same
distribution as running `prog` against `counterRealHandler hash k` from `pads`. -/
theorem uniform_bind_run_interpret_counterSeqHandler
    {ι α : Type} [DecidableEq ι] [Fintype ι] [Fintype Y] [Nonempty Y]
    (hash : K → M → Y) (k : K) (nonce : ℕ → ι)
    {prog : OracleComp (fun _ : M => Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (pads : List (M × Y))
    (hinj : ∀ i, pads.length ≤ i → i < pads.length + Q →
      ∀ j, pads.length ≤ j → j < pads.length + Q → nonce i = nonce j → i = j) :
    ((PMF.uniformOfFintype (ι → Y)).bind fun table =>
      (OracleComp.interpret (counterSeqHandler hash k (fun i => table (nonce i))) prog).run pads) =
      (OracleComp.interpret (counterRealHandler hash k) prog).run pads := by
  induction hprog generalizing pads with
  | pure a Q =>
    simp [PMF.monad_pure_eq_pure]
  | liftBind m cont Q hcont ih =>
    rw [← PMF.uniformOfFintype_update (γ := Y) (nonce pads.length), PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def, OracleComp.interpret_bind,
      OracleComp.interpret_query, StateT.run_bind, PMF.monad_bind_eq_bind,
      run_counterSeqHandler, run_counterRealHandler, PMF.bind_bind, PMF.pure_bind,
      Function.update_self]
    congr 1
    funext r
    have hcongr (table : ι → Y) :
        (OracleComp.interpret
          (counterSeqHandler hash k fun i => Function.update table (nonce pads.length) r (nonce i))
          (cont (sign hash k r m))).run (pads ++ [(m, r)]) =
        (OracleComp.interpret
          (counterSeqHandler hash k fun i => table (nonce i))
          (cont (sign hash k r m))).run (pads ++ [(m, r)]) := by
      refine run_interpret_counterSeqHandler_congr hash k (hcont (sign hash k r m))
        (pads ++ [(m, r)]) fun i hlo hhi => ?_
      simp only [List.length_append, List.length_singleton] at hlo hhi
      have hne : nonce i ≠ nonce pads.length := fun heq => by
        have := hinj i (by omega) (by omega) pads.length (le_refl _) (by omega) heq
        omega
      exact Function.update_of_ne hne r table
    simp only [hcongr]
    exact ih (sign hash k r m) (pads ++ [(m, r)]) fun i hi₁ hi₂ j hj₁ hj₂ heq => by
      simp only [List.length_append, List.length_singleton] at hi₁ hi₂ hj₁ hj₂
      exact hinj i (by omega) (by omega) j (by omega) (by omega) heq

variable [DecidableEq M] [DecidableEq Y]

/-- The issued-slot EUF-CMA experiment for the counter Carter–Wegman MAC under an arbitrary
pad-sequence distribution `padSeqDist : PMF (ℕ → Y)`. -/
noncomputable def maskedCounterSlotGame (seed : PMF K) (padSeqDist : PMF (ℕ → Y))
    (hash : K → M → Y) (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let padSeq ← padSeqDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterSeqHandler hash k padSeq) (forger.forge s)).run []
  return checkCounterSlot hash k res.2 res.1

/-- The issued-counter global-message-freshness EUF-CMA experiment under an arbitrary
pad-sequence distribution `padSeqDist : PMF (ℕ → Y)`. -/
noncomputable def maskedCounterGame (seed : PMF K) (padSeqDist : PMF (ℕ → Y))
    (hash : K → M → Y) (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let padSeq ← padSeqDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterSeqHandler hash k padSeq) (forger.forge s)).run []
  return checkCounterEUF hash k res.2 res.1

/-- The issued-slot strong SUF-CMA experiment under an arbitrary pad-sequence distribution
`padSeqDist : PMF (ℕ → Y)`. -/
noncomputable def maskedCounterStrongGame (seed : PMF K) (padSeqDist : PMF (ℕ → Y))
    (hash : K → M → Y) (forger : CounterForger M Y) : PMF Bool := do
  let k ← seed
  let padSeq ← padSeqDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterSeqHandler hash k padSeq) (forger.forge s)).run []
  return checkCounterSUF hash k res.2 res.1

theorem maskedCounterStrongGame_eq_maskedCounterSlotGame (seed : PMF K)
    (padSeqDist : PMF (ℕ → Y)) (hash : K → M → Y) (forger : CounterForger M Y) :
    maskedCounterStrongGame seed padSeqDist hash forger =
      maskedCounterSlotGame seed padSeqDist hash forger := by
  dsimp only [maskedCounterStrongGame, maskedCounterSlotGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  congr 1; funext k; congr 1; funext padSeq; congr 1; funext s; congr 1; funext res
  rw [checkCounterSUF_eq_checkCounterSlot]

theorem maskedCounterGame_le_maskedCounterSlotGame (seed : PMF K) (padSeqDist : PMF (ℕ → Y))
    (hash : K → M → Y) (forger : CounterForger M Y) :
    maskedCounterGame seed padSeqDist hash forger true ≤
      maskedCounterSlotGame seed padSeqDist hash forger true := by
  dsimp only [maskedCounterGame, maskedCounterSlotGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  refine bind_apply_mono_on_support seed true fun k _ => ?_
  refine bind_apply_mono_on_support padSeqDist true fun padSeq _ => ?_
  refine bind_apply_mono_on_support forger.coins true fun s _ => ?_
  refine bind_apply_mono_on_support
    ((OracleComp.interpret (counterSeqHandler hash k padSeq) (forger.forge s)).run []) true
    fun res _ => ?_
  by_cases h : checkCounterEUF hash k res.2 res.1 = true
  · rw [h, checkCounterEUF_imp_checkCounterSlot hash k res.2 res.1 h]
  · simp [Bool.eq_false_iff.mpr h]

/-- The induced multi-query pad-sequence distinguisher `(ℕ → Y) → PMF Bool` that samples `k ← seed`
and `s ← forger.coins`, simulates `forger.forge s` using `counterSeqHandler hash k padSeq`, and
evaluates `checkCounterSlot hash k`. -/
noncomputable def counterPadSeqDistinguisher (seed : PMF K) (hash : K → M → Y)
    (forger : CounterForger M Y) (padSeq : ℕ → Y) : PMF Bool := do
  let k ← seed
  let s ← forger.coins
  let res ← (OracleComp.interpret (counterSeqHandler hash k padSeq) (forger.forge s)).run []
  return checkCounterSlot hash k res.2 res.1

theorem maskedCounterSlotGame_eq_bind_counterPadSeqDistinguisher (seed : PMF K)
    (padSeqDist : PMF (ℕ → Y)) (hash : K → M → Y) (forger : CounterForger M Y) :
    maskedCounterSlotGame seed padSeqDist hash forger =
      padSeqDist.bind (counterPadSeqDistinguisher seed hash forger) :=
  PMF.bind_comm seed padSeqDist _

/-- If `forger` makes at most `Q` signing queries, then `counterPadSeqDistinguisher` depends only on
the first `Q` pads `padSeq 0, ..., padSeq (Q - 1)`. -/
theorem counterPadSeqDistinguisher_congr (seed : PMF K) (hash : K → M → Y)
    {forger : CounterForger M Y} {Q : ℕ} (hforger : ∀ s, (forger.forge s).IsQueryBounded Q)
    {padSeq₁ padSeq₂ : ℕ → Y} (hpad : ∀ i < Q, padSeq₁ i = padSeq₂ i) :
    counterPadSeqDistinguisher seed hash forger padSeq₁ =
      counterPadSeqDistinguisher seed hash forger padSeq₂ := by
  dsimp only [counterPadSeqDistinguisher, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  congr 1; funext k; congr 1; funext s
  rw [run_interpret_counterSeqHandler_congr hash k (hforger s) []
    (fun i _ hi => hpad i (by simpa using hi))]

/-- When `table ← PMF.uniformOfFintype (ι → Y)` and `nonce : ℕ → ι` is injective on
`{0, ..., Q - 1}`, sampling `table` and running `counterPadSeqDistinguisher` on
`fun i => table (nonce i)` has the exact same distribution as `counterSlotGame seed hash forger`. -/
theorem uniform_bind_counterPadSeqDistinguisher
    {ι : Type} [DecidableEq ι] [Fintype ι] [Fintype Y] [Nonempty Y]
    (seed : PMF K) (hash : K → M → Y) (nonce : ℕ → ι)
    {forger : CounterForger M Y} {Q : ℕ} (hforger : ∀ s, (forger.forge s).IsQueryBounded Q)
    (hinj : ∀ i < Q, ∀ j < Q, nonce i = nonce j → i = j) :
    ((PMF.uniformOfFintype (ι → Y)).bind fun table =>
      counterPadSeqDistinguisher seed hash forger (fun i => table (nonce i))) =
      counterSlotGame seed hash forger := by
  dsimp only [counterPadSeqDistinguisher, counterSlotGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  rw [PMF.bind_comm (PMF.uniformOfFintype (ι → Y)) seed]
  congr 1; funext k
  rw [PMF.bind_comm (PMF.uniformOfFintype (ι → Y)) forger.coins]
  congr 1; funext s
  rw [← PMF.bind_bind,
    uniform_bind_run_interpret_counterSeqHandler hash k nonce (hforger s) []
      (fun i _ hi j _ hj heq => hinj i (by simpa using hi) j (by simpa using hj) heq)]

/-- The multi-query pad-sequence distribution on `ℕ → BitString n` obtained by sampling a uniform
`n`-bit PRF key `key ← BitString.uniformList n` and evaluating `prfOracle family n key (nonce i)` at
each counter index `i`. -/
noncomputable def prfPadSeqDist (family : List Bool → List Bool → List Bool) (n : ℕ)
    (nonce : ℕ → List Bool) : PMF (ℕ → BitString n) :=
  (BitString.uniformList n).map fun key i =>
    BitString.ofList n (prfOracle family n key (nonce i))

/-- The multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot EUF-CMA experiment
(after [BonehShoup2023], Section 7.5, Theorem 7.10), where the signer's counter schedule `nonce`
fixes the nonces and `checkCounterSlot` accepts only issued counter indices (`pads[idx]? = some r`),
rejecting unissued `idx`. -/
noncomputable def prfCounterSlotGame (seed : PMF K) (family : List Bool → List Bool → List Bool)
    (n : ℕ) (nonce : ℕ → List Bool) (hash : K → M → BitString n)
    (forger : CounterForger M (BitString n)) : PMF Bool :=
  maskedCounterSlotGame seed (prfPadSeqDist family n nonce) hash forger

/-- The multi-query fresh-nonce PRF-masked Carter–Wegman issued-counter EUF-CMA experiment
(after [BonehShoup2023], Section 7.5, Theorem 7.10), where the signer's counter schedule `nonce`
fixes the nonces and `checkCounterGlobal` accepts only issued counter indices
(`pads[idx]? = some r`), rejecting unissued `idx`. -/
noncomputable def prfCounterGame (seed : PMF K) (family : List Bool → List Bool → List Bool)
    (n : ℕ) (nonce : ℕ → List Bool) (hash : K → M → BitString n)
    (forger : CounterForger M (BitString n)) : PMF Bool :=
  maskedCounterGame seed (prfPadSeqDist family n nonce) hash forger

/-- The multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot strong SUF-CMA experiment
(after [BonehShoup2023], Section 7.5, Theorem 7.10), where the signer's counter schedule `nonce`
fixes the nonces and `checkCounterStrong` accepts only issued counter indices
(`pads[idx]? = some r`), rejecting unissued `idx`. -/
noncomputable def prfCounterStrongGame (seed : PMF K) (family : List Bool → List Bool → List Bool)
    (n : ℕ) (nonce : ℕ → List Bool) (hash : K → M → BitString n)
    (forger : CounterForger M (BitString n)) : PMF Bool :=
  maskedCounterStrongGame seed (prfPadSeqDist family n nonce) hash forger

theorem prfCounterStrongGame_eq_prfCounterSlotGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (nonce : ℕ → List Bool)
    (hash : K → M → BitString n) (forger : CounterForger M (BitString n)) :
    prfCounterStrongGame seed family n nonce hash forger =
      prfCounterSlotGame seed family n nonce hash forger :=
  maskedCounterStrongGame_eq_maskedCounterSlotGame seed (prfPadSeqDist family n nonce) hash forger

theorem prfCounterGame_le_prfCounterSlotGame (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (n : ℕ) (nonce : ℕ → List Bool)
    (hash : K → M → BitString n) (forger : CounterForger M (BitString n)) :
    prfCounterGame seed family n nonce hash forger true ≤
      prfCounterSlotGame seed family n nonce hash forger true :=
  maskedCounterGame_le_maskedCounterSlotGame seed (prfPadSeqDist family n nonce) hash forger

/-- One step of multi-pad collection at security parameter `n` under nonce schedule `nonce`:
query the external oracle at `nonce n pads.length`, take at most `n` reply bits, and append the
reply to `pads`. -/
def prfPadCollectStep (n : ℕ) (nonce : ℕ → ℕ → List Bool) (pads : List (List Bool)) :
    WordOracleComp Unit (List (List Bool)) :=
  (fun reply => pads ++ [reply]) <$>
    (List.take n <$> ProbOracleComp.query ((), nonce n pads.length))

/-- Multi-query PRF `OracleDistinguisher` for a query budget `Q : ℕ → ℕ`, nonce schedule
`nonce : ℕ → ℕ → List Bool`, and pad-sequence test
`test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool`: at security parameter `n`, collect `Q n`
oracle replies at `nonce n 0, ..., nonce n (Q n - 1)` and run `test n` on the `n`-bit views of the
collected replies. -/
def prfMultiPadDistinguisher (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool) : OracleDistinguisher :=
  fun n _ => do
    let replies ← OracleComp.iterate (Q n) (prfPadCollectStep n nonce) []
    ProbOracleComp.sample (test n (fun i => BitString.ofList n (replies.getD i [])))

private theorem interpret_iterate_prfPadCollectStep (n : ℕ) (nonce : ℕ → ℕ → List Bool)
    (f : List Bool → List Bool) (q : ℕ) (init : List (List Bool)) :
    OracleComp.interpret
      (ProbOracleComp.handler ProbComp.unifFin (fun request => pure (f request.2)))
      (OracleComp.iterate q (prfPadCollectStep n nonce) init) =
      pure (init ++ (List.range q).map (fun i => (f (nonce n (init.length + i))).take n)) := by
  induction q generalizing init with
  | zero =>
    simp [OracleComp.iterate]
  | succ q ih =>
    simp only [OracleComp.iterate_succ, prfPadCollectStep, OracleComp.interpret_bind,
      OracleComp.interpret_map, ProbOracleComp.interpret_query, pure_bind, Functor.map_map,
      map_pure, ih, List.length_append, List.length_map, List.length_range, List.range_succ,
      List.map_append, List.map_singleton, List.append_assoc]

private theorem ofList_getD_map_range_take (n q : ℕ) (g : ℕ → List Bool) {i : ℕ} (hi : i < q) :
    BitString.ofList n (((List.range q).map (fun j => (g j).take n)).getD i []) =
      BitString.ofList n (g i) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]), Option.getD_some,
    List.getElem_map, List.getElem_range, ofList_take]

/-- In `prfRealGame`, when `forger` makes at most `Q n` signing queries and `test n` realizes
`counterPadSeqDistinguisher seed hash forger`, `prfMultiPadDistinguisher Q nonce test` has the exact
outcome distribution of `prfCounterSlotGame seed family n (nonce n) hash forger`. -/
theorem eval_prfRealGame_prfMultiPadDistinguisher {n : ℕ} (seed : PMF K)
    (family : List Bool → List Bool → List Bool) (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool)
    (hash : K → M → BitString n) {forger : CounterForger M (BitString n)}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded (Q n))
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest : ∀ padSeq, counterPadSeqDistinguisher seed hash forger padSeq =
      ProbComp.eval (test n padSeq)) :
    ProbComp.eval (prfRealGame family (prfMultiPadDistinguisher Q nonce test) n) =
      prfCounterSlotGame seed family n (nonce n) hash forger := by
  rw [prfCounterSlotGame, maskedCounterSlotGame_eq_bind_counterPadSeqDistinguisher]
  simp only [prfRealGame, prfMultiPadDistinguisher, prfPadSeqDist,
    OracleComp.interpret_bind, interpret_iterate_prfPadCollectStep, List.nil_append,
    List.length_nil, Nat.zero_add, pure_bind, ProbOracleComp.interpret_sample,
    ProbComp.eval_bind, BitString.eval_sampleList, PMF.bind_map, Function.comp_def]
  simp only [show ProbComp.unifFin = OracleComp.query from rfl, OracleComp.interpret_query_eq_self]
  congr 1; funext key
  rw [← htest]
  exact counterPadSeqDistinguisher_congr seed hash hforger fun i hi =>
    ofList_getD_map_range_take n (Q n) (fun j => prfOracle family n key (nonce n j)) hi

/-- In `prfIdealGame`, when `forger` makes at most `Q n` signing queries, each `nonce n i`
(`i < Q n`) has length `n`, the `Q n` nonces are pairwise distinct on `{0, ..., Q n - 1}`, and
`test n` realizes `counterPadSeqDistinguisher seed hash forger`,
`prfMultiPadDistinguisher Q nonce test` has the exact outcome distribution of the ideal
`counterSlotGame seed hash forger`. -/
theorem eval_prfIdealGame_prfMultiPadDistinguisher {n : ℕ} (seed : PMF K)
    (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool) (hash : K → M → BitString n)
    {forger : CounterForger M (BitString n)}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest : ∀ padSeq, counterPadSeqDistinguisher seed hash forger padSeq =
      ProbComp.eval (test n padSeq)) :
    ProbComp.eval (prfIdealGame (prfMultiPadDistinguisher Q nonce test) n) =
      counterSlotGame seed hash forger := by
  simp only [prfIdealGame, prfMultiPadDistinguisher,
    OracleComp.interpret_bind, interpret_iterate_prfPadCollectStep, List.nil_append,
    List.length_nil, Nat.zero_add, pure_bind, ProbOracleComp.interpret_sample,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  simp only [show ProbComp.unifFin = OracleComp.query from rfl, OracleComp.interpret_query_eq_self]
  have htable (table : BitString n → BitString n) :
      ProbComp.eval
        (test n fun i =>
          BitString.ofList n
            (((List.range (Q n)).map fun j =>
              (randomFunctionOracle n table (nonce n j)).take n).getD i [])) =
      counterPadSeqDistinguisher seed hash forger
        (fun i => table (BitString.ofList n (nonce n i))) := by
    rw [← htest]
    refine counterPadSeqDistinguisher_congr seed hash hforger fun i hi => ?_
    rw [ofList_getD_map_range_take n (Q n) (fun j => randomFunctionOracle n table (nonce n j)) hi]
    simp [randomFunctionOracle, hnonce_len i hi]
  simp only [htable]
  refine uniform_bind_counterPadSeqDistinguisher seed hash
    (fun i => BitString.ofList n (nonce n i)) hforger fun i hi j hj heq => ?_
  apply hnonce_inj i hi j hj
  rw [← BitString.ofFn_ofList (hnonce_len i hi), ← BitString.ofFn_ofList (hnonce_len j hj), heq]

/-- **Multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot reduction**
(after [BonehShoup2023], Section 7.5, Theorem 7.10): when `hash` is `ε`-almost-Δ-universal
(`ε ≠ ⊤`), `forger` makes at most `Q n` signing queries, and `nonce n 0, ..., nonce n (Q n - 1)`
are pairwise distinct `n`-bit nonces fixed by the signer's counter schedule, the real-valued
issued-slot forgery probability in `prfCounterSlotGame` is at most `ε.toReal` plus the concrete PRF
distinguishing advantage of `prfMultiPadDistinguisher Q nonce test` at parameter `n` (with
unissued counter indices rejected by `checkCounterSlot`). -/
theorem prfCounterSlotGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool)
    {forger : CounterForger M (BitString n)}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest : ∀ padSeq, counterPadSeqDistinguisher seed hash forger padSeq =
      ProbComp.eval (test n padSeq)) :
    (prfCounterSlotGame seed family n (nonce n) hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfMultiPadDistinguisher Q nonce test) n))
          (ProbComp.eval (prfIdealGame (prfMultiPadDistinguisher Q nonce test) n)) : ℝ) := by
  rw [eval_prfRealGame_prfMultiPadDistinguisher seed family Q nonce hash hforger test htest,
    eval_prfIdealGame_prfMultiPadDistinguisher seed Q nonce hash hforger hnonce_len hnonce_inj
      test htest,
    Game.coe_advantage, Game.coe_succProbability, Game.coe_succProbability]
  have hle : (counterSlotGame seed hash forger true).toReal ≤ ε.toReal :=
    ENNReal.toReal_mono hε (counterSlotGame_le hh forger)
  linarith [le_abs_self ((prfCounterSlotGame seed family n (nonce n) hash forger true).toReal -
    (counterSlotGame seed hash forger true).toReal)]

/-- **Multi-query fresh-nonce PRF-masked Carter–Wegman issued-counter EUF-CMA reduction**
(after [BonehShoup2023], Section 7.5, Theorem 7.10). -/
theorem prfCounterGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool)
    {forger : CounterForger M (BitString n)}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest : ∀ padSeq, counterPadSeqDistinguisher seed hash forger padSeq =
      ProbComp.eval (test n padSeq)) :
    (prfCounterGame seed family n (nonce n) hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfMultiPadDistinguisher Q nonce test) n))
          (ProbComp.eval (prfIdealGame (prfMultiPadDistinguisher Q nonce test) n)) : ℝ) := by
  have hmono : (prfCounterGame seed family n (nonce n) hash forger true).toReal ≤
      (prfCounterSlotGame seed family n (nonce n) hash forger true).toReal :=
    ENNReal.toReal_mono (PMF.apply_ne_top _ _)
      (prfCounterGame_le_prfCounterSlotGame seed family n (nonce n) hash forger)
  exact hmono.trans
    (prfCounterSlotGame_le hh hε family Q nonce hforger hnonce_len hnonce_inj test htest)

/-- **Multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot SUF-CMA reduction**
(after [BonehShoup2023], Section 7.5, Theorem 7.10). -/
theorem prfCounterStrongGame_le {n : ℕ} {seed : PMF K} {hash : K → M → BitString n} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) (hε : ε ≠ ⊤)
    (family : List Bool → List Bool → List Bool)
    (Q : ℕ → ℕ) (nonce : ℕ → ℕ → List Bool)
    {forger : CounterForger M (BitString n)}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest : ∀ padSeq, counterPadSeqDistinguisher seed hash forger padSeq =
      ProbComp.eval (test n padSeq)) :
    (prfCounterStrongGame seed family n (nonce n) hash forger true).toReal ≤
      ε.toReal +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfMultiPadDistinguisher Q nonce test) n))
          (ProbComp.eval (prfIdealGame (prfMultiPadDistinguisher Q nonce test) n)) : ℝ) := by
  rw [prfCounterStrongGame_eq_prfCounterSlotGame]
  exact prfCounterSlotGame_le hh hε family Q nonce hforger hnonce_len hnonce_inj test htest

/-- `prfMultiPadDistinguisher Q nonce test` is uniformly strict oracle-PPT (`IsOraclePPT encBool`)
whenever the query budget `Q`, the nonce schedule `nonce`, and the pad-list test `test` are
uniformly polynomial-time / strict PPT. -/
theorem isOraclePPT_prfMultiPadDistinguisher
    {Q : ℕ → ℕ} {nonce : ℕ → ℕ → List Bool}
    {test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool}
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hnonce : ComputableInPolyTime (fun p : ℕ × ℕ => nonce p.1 p.2)
      (encPair encUnary encUnary) encBits)
    (htest : IsPPTOn (encPair encUnary (encList encBits)) encBool
      (fun p : ℕ × List (List Bool) =>
        test p.1 (fun i => BitString.ofList p.1 (p.2.getD i [])))) :
    IsOraclePPT encBool (prfMultiPadDistinguisher Q nonce test) := by
  have hQ_tidy := hQ.tidy
  have hnonce_tidy := hnonce.tidy
  have hq : IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encList encBits))
      encBits
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        List.take p.1.1 <$> ProbOracleComp.query ((), nonce p.1.1 p.2.length)) :=
    IsOraclePPTOn.query_take () (by polytime) (by polytime)
  have hstep : IsOraclePPTOn
      (encPair (encPair encUnary encBits) (encList encBits))
      (encList encBits)
      (fun p : (ℕ × List Bool) × List (List Bool) =>
        prfPadCollectStep p.1.1 nonce p.2) := by
    unfold prfPadCollectStep
    exact hq.map_with
      (f := fun (p : (ℕ × List Bool) × List (List Bool)) reply => p.2 ++ [reply])
      (by polytime)
  have hpoly : PolyBounded (fun p : ℕ × List Bool => (encPair encUnary encBits p).length)
      (fun p : ℕ × List Bool => 2 * p.1 + 2) := by
    have h1 : ComputableTidilyInPolyTime (fun p : ℕ × List Bool => 2 * p.1 + 2)
        (encPair encUnary encBits) encUnary := by polytime
    simpa only [encUnary_apply, List.length_replicate] using h1.polyBounded_length
  have hiter : IsOraclePPTOn (encPair encUnary encBits) (encList encBits)
      (fun p : ℕ × List Bool =>
        OracleComp.iterate (Q p.1) (prfPadCollectStep p.1 nonce) []) := by
    refine IsOraclePPTOn.iterateWith_of_bounded_growth
      (initial := fun _ : ℕ × List Bool => ([] : List (List Bool)))
      (count := fun p : ℕ × List Bool => Q p.1)
      (step := fun (p : ℕ × List Bool) pads => prfPadCollectStep p.1 nonce pads)
      (by polytime) (by polytime) hstep hpoly ?_
    intro p pads next hnext
    unfold prfPadCollectStep at hnext
    obtain ⟨reply, hreply, rfl⟩ := ProbOracleComp.mem_support_map hnext
    obtain ⟨rawReply, _, rfl⟩ := ProbOracleComp.mem_support_map hreply
    have hlen : (rawReply.take p.1).length ≤ p.1 := List.length_take_le _ _
    simp only [encList_append, encList_cons, encList_nil, List.append_nil, List.length_append,
      length_frame, encBits_apply]
    omega
  unfold prfMultiPadDistinguisher
  exact (hiter.bind_with ((htest.preprocess
    (prepare := fun p : (ℕ × List Bool) × List (List Bool) => (p.1.1, p.2))
    (by polytime)).isOraclePPTOn)).isOraclePPT

/-- **Asymptotic multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot security**
(after [BonehShoup2023], Section 7.5, Theorem 7.10). The query bound `hforger` and nonce
conditions `hnonce_len`, `hnonce_inj` are required only eventually (`∀ᶠ n in Filter.atTop`), so
any polynomial query budget `Q n` (where `Q n ≤ 2 ^ n` holds for all sufficiently large `n`) is
covered without patching small `n`. -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfCounterSlotGame
    {K M : ℕ → Type} [∀ n, DecidableEq (M n)]
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : (n : ℕ) → PMF (K n)} {hash : (n : ℕ) → K n → M n → BitString n}
    {ε : ℕ → ℝ≥0} (hh : ∀ n, IsDeltaUniversalHash (seed n) (hash n) (ε n))
    (hε : Negligible ε)
    {Q : ℕ → ℕ} {nonce : ℕ → ℕ → List Bool}
    (forger : (n : ℕ) → CounterForger (M n) (BitString n))
    (hforger : ∀ᶠ n in Filter.atTop, ∀ s, ((forger n).forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ᶠ n in Filter.atTop, ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ᶠ n in Filter.atTop, ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest_eval : ∀ n padSeq,
      counterPadSeqDistinguisher (seed n) (hash n) (forger n) padSeq =
        ProbComp.eval (test n padSeq))
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hnonce : ComputableInPolyTime (fun p : ℕ × ℕ => nonce p.1 p.2)
      (encPair encUnary encUnary) encBits)
    (htest_ppt : IsPPTOn (encPair encUnary (encList encBits)) encBool
      (fun p : ℕ × List (List Bool) =>
        test p.1 (fun i => BitString.ofList p.1 (p.2.getD i [])))) :
    Negligible (fun n =>
      Game.succProbability
        (prfCounterSlotGame (seed n) family n (nonce n) (hash n) (forger n))) := by
  have hdist := hprf.secure (prfMultiPadDistinguisher Q nonce test)
    (isOraclePPT_prfMultiPadDistinguisher hQ hnonce htest_ppt)
  refine negligible_of_eventually_le (hε.add hdist) ?_
  filter_upwards [hforger, hnonce_len, hnonce_inj] with n hforger_n hlen_n hinj_n
  rw [← NNReal.coe_le_coe, Game.coe_succProbability, Pi.add_apply, NNReal.coe_add]
  simpa only [ENNReal.coe_toReal] using
    prfCounterSlotGame_le (hh n) ENNReal.coe_ne_top family Q nonce hforger_n
      hlen_n hinj_n test (htest_eval n)

/-- **Asymptotic multi-query fresh-nonce PRF-masked Carter–Wegman issued-counter EUF-CMA security**
(after [BonehShoup2023], Section 7.5, Theorem 7.10). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfCounterGame
    {K M : ℕ → Type} [∀ n, DecidableEq (M n)]
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : (n : ℕ) → PMF (K n)} {hash : (n : ℕ) → K n → M n → BitString n}
    {ε : ℕ → ℝ≥0} (hh : ∀ n, IsDeltaUniversalHash (seed n) (hash n) (ε n))
    (hε : Negligible ε)
    {Q : ℕ → ℕ} {nonce : ℕ → ℕ → List Bool}
    (forger : (n : ℕ) → CounterForger (M n) (BitString n))
    (hforger : ∀ᶠ n in Filter.atTop, ∀ s, ((forger n).forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ᶠ n in Filter.atTop, ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ᶠ n in Filter.atTop, ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest_eval : ∀ n padSeq,
      counterPadSeqDistinguisher (seed n) (hash n) (forger n) padSeq =
        ProbComp.eval (test n padSeq))
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hnonce : ComputableInPolyTime (fun p : ℕ × ℕ => nonce p.1 p.2)
      (encPair encUnary encUnary) encBits)
    (htest_ppt : IsPPTOn (encPair encUnary (encList encBits)) encBool
      (fun p : ℕ × List (List Bool) =>
        test p.1 (fun i => BitString.ofList p.1 (p.2.getD i [])))) :
    Negligible (fun n =>
      Game.succProbability
        (prfCounterGame (seed n) family n (nonce n) (hash n) (forger n))) := by
  refine negligible_of_le
    (hprf.negligible_prfCounterSlotGame hh hε forger hforger hnonce_len hnonce_inj test
      htest_eval hQ hnonce htest_ppt) fun n => ?_
  exact ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
    (prfCounterGame_le_prfCounterSlotGame (seed n) family n (nonce n) (hash n) (forger n))

/-- **Asymptotic multi-query fresh-nonce PRF-masked Carter–Wegman issued-slot SUF-CMA security**
(after [BonehShoup2023], Section 7.5, Theorem 7.10). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.negligible_prfCounterStrongGame
    {K M : ℕ → Type} [∀ n, DecidableEq (M n)]
    {family : List Bool → List Bool → List Bool} (hprf : PseudorandomFunction family)
    {seed : (n : ℕ) → PMF (K n)} {hash : (n : ℕ) → K n → M n → BitString n}
    {ε : ℕ → ℝ≥0} (hh : ∀ n, IsDeltaUniversalHash (seed n) (hash n) (ε n))
    (hε : Negligible ε)
    {Q : ℕ → ℕ} {nonce : ℕ → ℕ → List Bool}
    (forger : (n : ℕ) → CounterForger (M n) (BitString n))
    (hforger : ∀ᶠ n in Filter.atTop, ∀ s, ((forger n).forge s).IsQueryBounded (Q n))
    (hnonce_len : ∀ᶠ n in Filter.atTop, ∀ i < Q n, (nonce n i).length = n)
    (hnonce_inj : ∀ᶠ n in Filter.atTop, ∀ i < Q n, ∀ j < Q n, nonce n i = nonce n j → i = j)
    (test : (k : ℕ) → (ℕ → BitString k) → ProbComp Bool)
    (htest_eval : ∀ n padSeq,
      counterPadSeqDistinguisher (seed n) (hash n) (forger n) padSeq =
        ProbComp.eval (test n padSeq))
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hnonce : ComputableInPolyTime (fun p : ℕ × ℕ => nonce p.1 p.2)
      (encPair encUnary encUnary) encBits)
    (htest_ppt : IsPPTOn (encPair encUnary (encList encBits)) encBool
      (fun p : ℕ × List (List Bool) =>
        test p.1 (fun i => BitString.ofList p.1 (p.2.getD i [])))) :
    Negligible (fun n =>
      Game.succProbability
        (prfCounterStrongGame (seed n) family n (nonce n) (hash n) (forger n))) := by
  simp only [prfCounterStrongGame_eq_prfCounterSlotGame]
  exact hprf.negligible_prfCounterSlotGame hh hε forger hforger hnonce_len hnonce_inj test
    htest_eval hQ hnonce htest_ppt

end PRFCounter

/-! ### Concrete Carter–Wegman instantiations -/

section Instantiations

/-- **Polynomial Carter–Wegman one-time MAC (`xpolyHash`)** ([BonehShoup2023], Section 7.4.1):
over a finite field `F`, authenticating messages of length at most `ℓ` via `xpolyHash` has
adaptive one-time EUF-CMA (and SUF-CMA) forgery probability at most `(ℓ + 1) / |F|`. -/
theorem oneTimeGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : OneTimeForger {m : List F // m.length ≤ ℓ} F) :
    oneTimeGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  oneTimeGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Polynomial Carter–Wegman multi-query issued-counter MAC (`xpolyHash`)**:
authenticating messages of length at most `ℓ` via `xpolyHash` with fresh pads per query has
adaptive multi-query issued-counter EUF-CMA forgery probability at most `(ℓ + 1) / |F|`. -/
theorem counterGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : CounterForger {m : List F // m.length ≤ ℓ} F) :
    counterGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  counterGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Polynomial Carter–Wegman multi-query issued-slot strong unforgeability (`xpolyHash`)**. -/
theorem counterStrongGame_xpolyHash_le {F : Type} [Field F] [Fintype F] [DecidableEq F] (ℓ : ℕ)
    (forger : CounterForger {m : List F // m.length ≤ ℓ} F) :
    counterStrongGame (PMF.uniformOfFintype F)
      (fun k (m : {m : List F // m.length ≤ ℓ}) => xpolyHash k m) forger true ≤
      (ℓ + 1) / Fintype.card F :=
  counterStrongGame_le (isDeltaUniversalHash_xpolyHash ℓ) forger

/-- **Boolean-matrix Carter–Wegman one-time MAC (`BitString.LinearHash.hash`)**:
hashing `n`-bit messages to `m`-bit tags with a uniform Boolean matrix has adaptive one-time
forgery probability at most `2⁻ᵐ`. -/
theorem oneTimeGame_linearHash_le (n m : ℕ)
    (forger : OneTimeForger (BitString n) (BitString m)) :
    oneTimeGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    oneTimeGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Boolean-matrix Carter–Wegman multi-query issued-counter MAC (`BitString.LinearHash.hash`)**:
adaptive multi-query issued-counter EUF-CMA forgery probability is at most `2⁻ᵐ`. -/
theorem counterGame_linearHash_le (n m : ℕ)
    (forger : CounterForger (BitString n) (BitString m)) :
    counterGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    counterGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Boolean-matrix Carter–Wegman multi-query issued-slot strong unforgeability
(`BitString.LinearHash.hash`)**. -/
theorem counterStrongGame_linearHash_le (n m : ℕ)
    (forger : CounterForger (BitString n) (BitString m)) :
    counterStrongGame (PMF.uniformOfFintype (Fin m → BitString n))
      BitString.LinearHash.hash forger true ≤ ((2 : ℝ≥0∞) ^ m)⁻¹ := by
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    counterStrongGame_le (BitString.LinearHash.isDeltaUniversalHash n m) forger

/-- **Exact single-query PRF-pad reduction for Boolean-matrix Carter–Wegman
(`BitString.LinearHash.hash`)** in the one-query, fixed-nonce case (after [BonehShoup2023],
Section 7.4): hashing `n`-bit messages to `m`-bit tags with a uniform Boolean matrix and masking by
a fixed-nonce PRF evaluation at security parameter `m` has real-valued one-time forgery probability
at most `(2 ^ m)⁻¹` plus the concrete PRF distinguishing advantage of `prfPadDistinguisher test` at
parameter `m` (without asserting `IsOraclePPT encBool` admissibility or an asymptotic
`PseudorandomFunction` corollary). -/
theorem prfOneTimeGame_linearHash_le (n m : ℕ)
    (family : List Bool → List Bool → List Bool)
    (forger : OneTimeForger (BitString n) (BitString m))
    (test : (k : ℕ) → BitString k → ProbComp Bool)
    (htest : ∀ r,
      padDistinguisher (PMF.uniformOfFintype (Fin m → BitString n))
        BitString.LinearHash.hash forger r = ProbComp.eval (test m r)) :
    (prfOneTimeGame (PMF.uniformOfFintype (Fin m → BitString n)) family m
      BitString.LinearHash.hash forger true).toReal ≤
      ((2 : ℝ) ^ m)⁻¹ +
        (Game.advantage
          (ProbComp.eval (prfRealGame family (prfPadDistinguisher test) m))
          (ProbComp.eval (prfIdealGame (prfPadDistinguisher test) m)) : ℝ) := by
  have hε : ((Fintype.card (BitString m) : ℝ≥0∞))⁻¹ ≠ ⊤ := by
    simp
  have h := prfOneTimeGame_le (BitString.LinearHash.isDeltaUniversalHash n m) hε family forger
    test htest
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat] using h

/-- **Subset-sum Carter–Wegman one-time MAC (`BitString.LinearHash` / `BitString.SubsetSum.hash`)**:
hashing binary words `ι → Bool` into a finite additive abelian group `G` via uniform subset-sum
weights has adaptive one-time forgery probability at most `1 / |G|`. -/
theorem oneTimeGame_subsetSum_le {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (forger : OneTimeForger (ι → Bool) G) :
    oneTimeGame (PMF.uniformOfFintype (ι → G)) BitString.SubsetSum.hash forger true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  oneTimeGame_le BitString.SubsetSum.isDeltaUniversalHash forger

/-- **Subset-sum Carter–Wegman multi-query issued-counter MAC (`BitString.SubsetSum.hash`)**:
adaptive multi-query issued-counter EUF-CMA forgery probability is at most `1 / |G|`. -/
theorem counterGame_subsetSum_le {ι G : Type} [Fintype ι] [DecidableEq ι]
    [AddCommGroup G] [Fintype G] [DecidableEq G]
    (forger : CounterForger (ι → Bool) G) :
    counterGame (PMF.uniformOfFintype (ι → G)) BitString.SubsetSum.hash forger true ≤
      (Fintype.card G : ℝ≥0∞)⁻¹ :=
  counterGame_le BitString.SubsetSum.isDeltaUniversalHash forger

/-- **Pairwise-independent Carter–Wegman one-time MAC**: any pairwise independent hash family
`hash : K → M → Y` into a finite additive group `Y` has adaptive one-time forgery probability at
most `1 / |Y|`. -/
theorem oneTimeGame_of_isPairwiseIndependentHash_le {K M Y : Type} [Fintype K] [Nonempty K]
    [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y] {hash : K → M → Y}
    (hh : IsPairwiseIndependentHash hash) (forger : OneTimeForger M Y) :
    oneTimeGame (PMF.uniformOfFintype K) hash forger true ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  oneTimeGame_le hh.isDeltaUniversalHash forger

/-- **Pairwise-independent Carter–Wegman multi-query issued-counter MAC**: any pairwise independent
hash family `hash : K → M → Y` has adaptive multi-query issued-counter forgery probability at most
`1 / |Y|`. -/
theorem counterGame_of_isPairwiseIndependentHash_le {K M Y : Type} [Fintype K] [Nonempty K]
    [AddGroup Y] [Fintype Y] [Nonempty Y] [DecidableEq M] [DecidableEq Y] {hash : K → M → Y}
    (hh : IsPairwiseIndependentHash hash) (forger : CounterForger M Y) :
    counterGame (PMF.uniformOfFintype K) hash forger true ≤ (Fintype.card Y : ℝ≥0∞)⁻¹ :=
  counterGame_le hh.isDeltaUniversalHash forger

end Instantiations

end Cslib.Crypto.Protocols.CarterWegman
