/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Reusable fuzzy extractors: definitions and the reduction steps for the common-matrix scheme

A fuzzy extractor `(Gen, Rep)` is *reusable* if its extracted key `r*` remains indistinguishable
from uniform even when the adversary observes multiple enrollments `Gen(w* + δ_i)` on correlated
readings derived from the same biometric source `w* ← W`. Following Apon, Cho, Eldefrawy, and Katz
([AponChoEldefrawyKatz2017], Sections 2.1–2.2, Definitions 2 and 3), we define the reusability
experiments in the public-parameters model over the Hamming space `Fin m → ZMod q`:

* A scheme is a family `fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper` parameterized by
  public parameters `pp : PP` drawn by a setup program `setup : ProbComp PP` and given to all
  parties.
* An adaptive adversary (`ReuseAdversary`) receives `(pp, p*)` from the challenge enrollment
  `(r*, p*) ← (fe pp).gen w*` and runs an oracle program: each query is a shift
  `δ : Fin m → ZMod q`, answered with a leakage value from a fresh enrollment
  `(r_i, p_i) ← (fe pp).gen (w* + clampShift t δ)`. `clampShift t` enforces the bound
  `hammingNorm δ ≤ t` of Definitions 2 and 3 by replacing an out-of-range shift with `0`. The
  program returns a saved state, and the challenge key (real or uniform) is given only after the
  queries, as in step 3 of Definitions 2 and 3. The number of queries is not fixed.
* In *weak reusability* (Definition 2), the leakage on each shift query is the helper `p_i` alone
  (`Leak = Helper`, `weakReuseOracle`).
* In *strong reusability* (Definition 3), the leakage on each shift query is both the helper and
  the extracted key `(p_i, r_i)` (`Leak = Helper × Key`, `strongReuseOracle`).
* Advantages (`weakReuseAdvantage`, `strongReuseAdvantage`) are defined as
  `Game.advantage realGame idealGame = |Pr[real] - Pr[ideal]|`, which is equivalent up to a factor
  of `2` to the paper's `1/2 + ε` guessing-game formulation.

This file defines the experiments and advantages only. It does not define a security predicate
"`fe` is reusable": such a predicate needs a class of efficient adversaries, which is future work.

In Section 3.3 ([AponChoEldefrawyKatz2017], Theorem 1), Apon et al. modify the Fuller–Meng–Reyzin
construction (`lweFuzzyExtractor`) by placing the random matrix `A ∈ Z_q^{m × (k + l)}` into the
common public parameters so that `Gen` samples only the secret `s` and outputs `c = A s + w`. We
formalize this construction as `commonMatrixFuzzyExtractor` and prove the reduction step of the
proof of Theorem 1 as an exact identity: for every source `W`, threshold `t` and weak-reuse
adversary `adv`, the weak-reuse advantage equals the single-enrollment `securityAdvantage` of
`lweFuzzyExtractor` against an explicit simulator `commonMatrixSimulator t adv` that answers each
shift `δ` with `c* + A s' + clampShift t δ` for a fresh uniform secret `s'`. Combining this
identity with `securityAdvantage_lweFuzzyExtractor_le` bounds the weak-reuse advantage of each
adversary by two decisional LWE advantages of explicit reductions. These are concrete reduction
lemmas, not the security theorem itself.

Correctness is stated averaged over the public parameters (`SetupCorrectHammingWithError`), and is
derived from the average-case decoder hypothesis `DecoderCorrectWithError` over a uniform matrix.

Finally, we formalize the observation of Section 3.3 (p. 10 of ePrint 2017/755) that
`commonMatrixFuzzyExtractor` is not strongly reusable: a 1-query strong-reuse attacker
(`commonMatrixStrongAttack`) querying `δ = 0` decodes `c* - c₁ = A (s* - s₁)` and adds `r₁` to
recover `r*`. If the decoder fails with probability at most `δ` on error `0`, the attacker's
strong-reuse advantage is at least `1 - δ - 1 / q ^ k`.

## Main definitions

* `Cslib.Crypto.FuzzyExtractor.ReuseAdversary`,
  `Cslib.Crypto.FuzzyExtractor.WeakReuseAdversary`,
  `Cslib.Crypto.FuzzyExtractor.StrongReuseAdversary`: adaptive reusability adversaries, whose query
  stage is an oracle program over shifts.
* `Cslib.Crypto.FuzzyExtractor.clampShift`: Hamming weight enforcement (`hammingNorm δ ≤ t`).
* `Cslib.Crypto.FuzzyExtractor.weakReuseOracle`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseRealGame`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseIdealGame`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage`: the experiment of Definition 2.
* `Cslib.Crypto.FuzzyExtractor.strongReuseOracle`,
  `Cslib.Crypto.FuzzyExtractor.strongReuseRealGame`,
  `Cslib.Crypto.FuzzyExtractor.strongReuseIdealGame`,
  `Cslib.Crypto.FuzzyExtractor.strongReuseAdvantage`: the experiment of Definition 3.
* `Cslib.Crypto.FuzzyExtractor.setupReproduceGame`,
  `Cslib.Crypto.FuzzyExtractor.SetupCorrectHammingWithError`: reproduction correctness with error
  `δ`, averaged over the public parameters.
* `Cslib.Crypto.FuzzyExtractor.commonMatrixFuzzyExtractor`,
  `Cslib.Crypto.FuzzyExtractor.commonMatrixSimulator`: the common-matrix FMR construction of
  Section 3.3 and the simulator from the proof of Theorem 1.
* `Cslib.Crypto.FuzzyExtractor.commonMatrixStrongAttack`: the 1-query strong-reusability attack on
  `commonMatrixFuzzyExtractor` (Section 3.3).

## Main results

* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_ofDistinguisher_eq_securityAdvantage`: a
  single-enrollment distinguisher, run as a weak-reuse adversary that makes no query, has its
  basic security advantage (the remark after Definition 2).
* `Cslib.Crypto.FuzzyExtractor.DecoderCorrectWithError.setupCorrect_commonMatrixFuzzyExtractor`:
  `δ`-error reproduction correctness of `commonMatrixFuzzyExtractor` over a uniform matrix.
* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_eq`: the reduction
  step of Theorem 1 as an exact advantage identity.
* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_le`: the
  weak-reuse advantage of each adversary is at most two decisional LWE advantages of explicit
  reductions.
* `Cslib.Crypto.FuzzyExtractor.strongReuseAdvantage_commonMatrixStrongAttack_ge`: the Section 3.3
  attack has strong-reuse advantage at least `1 - δ - 1 / q ^ k`.

## What is not proved

* A reusability security theorem. Here the adversary is any `ReuseAdversary`, with no efficiency
  bound. Concluding reusability needs an adversary class in the reuse experiments and efficiency
  certificates for `commonMatrixSimulator` and the reductions; this is concrete-only for now, and
  the certificates and asymptotic theorems are tracked in
  [#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6891722215).
* The Section 3.2 attack on independent-matrix FMR (`lweFuzzyExtractor` with fresh `A_i` per
  enrollment), which relies on the concrete `Decode_t` algorithm analysis.
* The Section 4 random-oracle transformation from weak to strong reusability (Theorem 2).
* Hardness of decisional LWE and concrete `Decode_t` success probability / running time.

## References

* [D. Apon, C. Cho, K. Eldefrawy, and J. Katz, *Efficient, Reusable Fuzzy Extractors from
  LWE*][AponChoEldefrawyKatz2017], Sections 2.1, 2.2, and 3.3 (Definitions 1–3, Theorem 1).
-/

public section

namespace Cslib.Crypto.FuzzyExtractor

open Probability
open scoped ENNReal NNReal

/-! ### Adaptive shift-query adversaries (Sections 2.1–2.2) -/

/-- An adaptive reusability adversary against a public-parameter fuzzy extractor over
`Fin m → ZMod q`, with saved state `σ` ([AponChoEldefrawyKatz2017], Definitions 2 and 3):
* `query pp p*` receives the public parameter `pp` and the challenge helper string `p*`, queries
  the shift oracle adaptively, each query `δ : Fin m → ZMod q` answered with the leakage `Leak` of
  a fresh enrollment on `w* + δ` (the helper string in weak reusability, the helper string and
  the key in strong reusability), and returns a saved state;
* `guess st r` receives the saved state and the challenge key candidate `r` and outputs a bit.

The key arrives only after the queries, as in step 3 of Definitions 2 and 3. The number of
queries is not fixed; a query bound is a property of `query` (`ProbOracleComp.IsQueryBounded`). -/
structure ReuseAdversary (PP : Type) (m q : ℕ) (Key Helper Leak σ : Type) where
  /-- Receive the public parameter and the challenge helper, query the shift oracle, and return
  a saved state. -/
  query : PP → Helper → ProbOracleComp (fun _ : Fin m → ZMod q => Leak) σ
  /-- Distinguish the real key `r*` from a uniform key, given the saved state. -/
  guess : σ → Key → ProbComp Bool

/-- A weak-reusability adversary (Definition 2): each shift query leaks only the helper string
`p_i : Helper`. -/
abbrev WeakReuseAdversary (PP : Type) (m q : ℕ) (Key Helper σ : Type) : Type :=
  ReuseAdversary PP m q Key Helper Helper σ

/-- A strong-reusability adversary (Definition 3): each shift query leaks both the helper string
and the extracted key `(p_i, r_i) : Helper × Key`. -/
abbrev StrongReuseAdversary (PP : Type) (m q : ℕ) (Key Helper σ : Type) : Type :=
  ReuseAdversary PP m q Key Helper (Helper × Key) σ

/-- Enforce the Hamming weight bound `hammingNorm δ ≤ t` required by Definitions 2 and 3: a shift
within the bound is kept unchanged, and an out-of-range shift is replaced by `0`. -/
@[expose] def clampShift {m q : ℕ} (t : ℕ) (δ : Fin m → ZMod q) : Fin m → ZMod q :=
  if hammingNorm δ ≤ t then δ else 0

/-- Every clamped shift has Hamming weight at most `t`. -/
theorem hammingNorm_clampShift_le {m q : ℕ} (t : ℕ) (δ : Fin m → ZMod q) :
    hammingNorm (clampShift t δ) ≤ t := by
  unfold clampShift
  split_ifs with h
  · exact h
  · simp

/-- A shift whose Hamming weight is already at most `t` is unchanged by `clampShift`. -/
theorem clampShift_of_le {m q : ℕ} {t : ℕ} {δ : Fin m → ZMod q} (h : hammingNorm δ ≤ t) :
    clampShift t δ = δ := by
  simp [clampShift, h]

/-- Clamping the zero shift always returns `0`. -/
@[simp] theorem clampShift_zero {m q : ℕ} (t : ℕ) :
    clampShift t (0 : Fin m → ZMod q) = 0 := by
  simp [clampShift]

/-! ### Definition 2: Weak reusability -/

section WeakReuse

variable {PP : Type} {m q : ℕ} {Key Helper σ : Type}

/-- The weak-reusability shift oracle on public parameter `pp` and reading `w*`
([AponChoEldefrawyKatz2017], Definition 2, step 2): on shift `δ`, run
`(fe pp).gen (w* + clampShift t δ)` and return the helper string. -/
@[expose] def weakReuseOracle (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper) (t : ℕ)
    (pp : PP) (w δ : Fin m → ZMod q) : ProbComp Helper := do
  let (_, p) ← (fe pp).gen (w + clampShift t δ)
  return p

/-- The real weak-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 2): sample `(r*, p*) ← (fe pp).gen w*`, run the query
stage of `adv` on `(pp, p*)` against `weakReuseOracle`, and pass `r*` to `adv.guess`. -/
@[expose] def weakReuseRealExperiment (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : WeakReuseAdversary PP m q Key Helper σ) : Experiment := do
  let (rStar, pStar) ← (fe pp).gen w
  let st ← (adv.query pp pStar).run (weakReuseOracle fe t pp w)
  adv.guess st rStar

/-- The ideal weak-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 2): as `weakReuseRealExperiment`, except `adv.guess`
receives an independent uniform key `u ← ProbComp.uniform Key` in place of `r*`. -/
@[expose] noncomputable def weakReuseIdealExperiment [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : WeakReuseAdversary PP m q Key Helper σ) : Experiment := do
  let (_, pStar) ← (fe pp).gen w
  let st ← (adv.query pp pStar).run (weakReuseOracle fe t pp w)
  let u ← ProbComp.uniform Key
  adv.guess st u

/-- The real weak-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 2). -/
@[expose] noncomputable def weakReuseRealGame (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper σ) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    weakReuseRealExperiment fe t pp w adv

/-- The ideal weak-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 2). -/
@[expose] noncomputable def weakReuseIdealGame [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper σ) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    weakReuseIdealExperiment fe t pp w adv

/-- The weak-reusability distinguishing advantage of `adv` on source `W` with shift queries of
Hamming weight at most `t` ([AponChoEldefrawyKatz2017], Definition 2). -/
noncomputable abbrev weakReuseAdvantage [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper σ) : ℝ≥0 :=
  Game.advantage (weakReuseRealGame setup fe W t adv) (weakReuseIdealGame setup fe W t adv)

end WeakReuse

/-! ### Definition 3: Strong reusability -/

section StrongReuse

variable {PP : Type} {m q : ℕ} {Key Helper σ : Type}

/-- The strong-reusability shift oracle on public parameter `pp` and reading `w*`
([AponChoEldefrawyKatz2017], Definition 3, step 2): on shift `δ`, run
`(r, p) ← (fe pp).gen (w* + clampShift t δ)` and return both `(p, r)`. -/
@[expose] def strongReuseOracle (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper) (t : ℕ)
    (pp : PP) (w δ : Fin m → ZMod q) : ProbComp (Helper × Key) := do
  let (r, p) ← (fe pp).gen (w + clampShift t δ)
  return (p, r)

/-- The real strong-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 3): sample `(r*, p*) ← (fe pp).gen w*`, run the query
stage of `adv` on `(pp, p*)` against `strongReuseOracle`, and pass `r*` to `adv.guess`. -/
@[expose] def strongReuseRealExperiment (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : StrongReuseAdversary PP m q Key Helper σ) : Experiment := do
  let (rStar, pStar) ← (fe pp).gen w
  let st ← (adv.query pp pStar).run (strongReuseOracle fe t pp w)
  adv.guess st rStar

/-- The ideal strong-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 3): as `strongReuseRealExperiment`, except `adv.guess`
receives an independent uniform key `u ← ProbComp.uniform Key` in place of `r*`. -/
@[expose] noncomputable def strongReuseIdealExperiment [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : StrongReuseAdversary PP m q Key Helper σ) : Experiment := do
  let (_, pStar) ← (fe pp).gen w
  let st ← (adv.query pp pStar).run (strongReuseOracle fe t pp w)
  let u ← ProbComp.uniform Key
  adv.guess st u

/-- The real strong-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 3). -/
@[expose] noncomputable def strongReuseRealGame (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper σ) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    strongReuseRealExperiment fe t pp w adv

/-- The ideal strong-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 3). -/
@[expose] noncomputable def strongReuseIdealGame [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper σ) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    strongReuseIdealExperiment fe t pp w adv

/-- The strong-reusability distinguishing advantage of `adv` on source `W` with shift queries of
Hamming weight at most `t` ([AponChoEldefrawyKatz2017], Definition 3). -/
noncomputable abbrev strongReuseAdvantage [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper σ) : ℝ≥0 :=
  Game.advantage (strongReuseRealGame setup fe W t adv)
    (strongReuseIdealGame setup fe W t adv)

end StrongReuse

/-! ### Weak reusability and basic security -/

section Relations

variable {PP : Type} {m q : ℕ} {Key Helper : Type}

/-- Embed a single-enrollment distinguisher `D : Key → Helper → Experiment` as a weak-reusability
adversary that makes no shift query and saves the challenge helper string `p*`. -/
def WeakReuseAdversary.ofDistinguisher (D : Key → Helper → Experiment) :
    WeakReuseAdversary PP m q Key Helper Helper where
  query _ pStar := pure pStar
  guess pStar r := D r pStar

/-- For a parameter-independent fuzzy extractor `fe₀` and any setup law `setup`, the
weak-reusability advantage of `WeakReuseAdversary.ofDistinguisher D` equals
`fe₀.securityAdvantage W D`: weak reusability implies security in the sense of Definition 1
([AponChoEldefrawyKatz2017], remark after Definition 2). -/
@[simp] theorem weakReuseAdvantage_ofDistinguisher_eq_securityAdvantage
    [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe₀ : FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) (D : Key → Helper → Experiment) :
    weakReuseAdvantage setup (fun _ => fe₀) W t (WeakReuseAdversary.ofDistinguisher D) =
      fe₀.securityAdvantage W D := by
  have hreal : weakReuseRealGame setup (fun _ => fe₀) W t
      (WeakReuseAdversary.ofDistinguisher D) = fe₀.realGame W D := by
    simp [weakReuseRealGame, FuzzyExtractor.realGame, Game.withSetup, weakReuseRealExperiment,
      FuzzyExtractor.realExperiment, WeakReuseAdversary.ofDistinguisher,
      ProbComp.eval_bind, PMF.bind_const]
  have hideal : weakReuseIdealGame setup (fun _ => fe₀) W t
      (WeakReuseAdversary.ofDistinguisher D) = fe₀.idealGame W D := by
    simp [weakReuseIdealGame, FuzzyExtractor.idealGame, Game.withSetup, weakReuseIdealExperiment,
      FuzzyExtractor.idealExperiment, WeakReuseAdversary.ofDistinguisher,
      ProbComp.eval_bind, PMF.bind_const]
  simp [weakReuseAdvantage, FuzzyExtractor.securityAdvantage, hreal, hideal]

end Relations

/-! ### Correctness averaged over the public parameters -/

section SetupCorrectness

variable {PP : Type} {m q : ℕ} {Key Helper : Type} [DecidableEq Key]

/-- The reproduction game averaged over the public parameters: sample `pp ← setup`, enroll `w`
with `(fe pp).gen`, reproduce from `w'` with `(fe pp).rep`, and test whether the keys agree. -/
@[expose] noncomputable def setupReproduceGame (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper) (w w' : Fin m → ZMod q) : Game :=
  (ProbComp.eval setup).bind fun pp => (fe pp).reproduceGame w w'

/-- Hamming reproduction correctness with error `δ`, averaged over the public parameters: for all
readings `w, w'` with `hammingDist w w' ≤ t`, `setupReproduceGame setup fe w w'` fails with
probability at most `δ`. This is the public-parameters form of `CorrectHammingWithError`; the
average over `setup` matches how [FullerMengReyzin2020] and [AponChoEldefrawyKatz2017] use an
average-case decoder over a uniform matrix. -/
@[expose] def SetupCorrectHammingWithError (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper) (t : ℕ) (δ : ℝ≥0) : Prop :=
  ∀ w w' : Fin m → ZMod q, hammingDist w w' ≤ t →
    Game.failProbability (setupReproduceGame setup fe w w') ≤ δ

end SetupCorrectness

/-! ### Section 3.3: Common-matrix FMR construction and Theorem 1 -/

section CommonMatrix

variable {m k l q : ℕ} [NeZero q]

/-- The modified FMR fuzzy extractor of [AponChoEldefrawyKatz2017], Section 3.3, parameterized by
the common public matrix `A : Matrix (Fin m) (Fin (k + l)) (ZMod q)`:
* `Gen(w)` samples a uniform secret `s : Fin (k + l) → ZMod q` and outputs the first `k`
  coordinates of `s` as the key together with the code-offset helper `c = A s + w`;
* `Rep(w', c)` runs `decode A (c - w')` and outputs the first `k` coordinates of the decoded
  secret (or `0` on `none`). -/
@[expose] noncomputable def commonMatrixFuzzyExtractor (m k l q : ℕ) [NeZero q]
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (A : Matrix (Fin m) (Fin (k + l)) (ZMod q)) :
    FuzzyExtractor (Fin m → ZMod q) (Fin k → ZMod q) (Fin m → ZMod q) where
  gen w := do
    let s ← ProbComp.uniform (Fin (k + l) → ZMod q)
    return (fun i => s (Fin.castAdd l i), A.mulVec s + w)
  rep w' c := do
    let sOpt ← decode A (c - w')
    match sOpt with
    | some s' => return fun i => s' (Fin.castAdd l i)
    | none => return 0

/-- `δ`-error decoder correctness over a uniform matrix (`DecoderCorrectWithError decode t δ`)
implies `δ`-error Hamming reproduction correctness of `commonMatrixFuzzyExtractor`, averaged over
a uniform common matrix `A` ([AponChoEldefrawyKatz2017], Section 3.3, correctness inherited from
[FullerMengReyzin2020], Theorem 4.11). -/
theorem DecoderCorrectWithError.setupCorrect_commonMatrixFuzzyExtractor
    {decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))}
    {t : ℕ} {δ : ℝ≥0} (hdec : DecoderCorrectWithError decode t δ) :
    SetupCorrectHammingWithError (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) t δ := by
  intro w w' hdis
  rw [hammingDist_comm, hammingDist_eq_hammingNorm, neg_add_eq_sub] at hdis
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [setupReproduceGame, FuzzyExtractor.reproduceGame, FuzzyExtractor.reproduceCheck,
    commonMatrixFuzzyExtractor, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (PMF.uniformOfFintype (Fin (k + l) → ZMod q))]
  refine PMF.bind_apply_le_on_support _ fun s _ => ?_
  simp only [add_sub_assoc]
  exact uniform_bind_decode_bind_apply_false_le_of_failProbability_le decode s (w - w') _
    (fun A => by simp) (hdec s (w - w') hdis)

/-- The simulator of [AponChoEldefrawyKatz2017], Theorem 1 (Section 3.3), as a single-enrollment
distinguisher against `lweFuzzyExtractor m k l q decode`: given key candidate `r` and helper
`p = ⟨A, c*, ()⟩`, it runs the query stage of `adv` on `(A, c*)`, answering each shift query `δ`
by sampling a fresh uniform `s' : Fin (k + l) → ZMod q` and returning `c* + A s' + clampShift t δ`,
and passes `r` to `adv.guess`. The simulator never sees the secret `s` or reading `w*`. -/
noncomputable def commonMatrixSimulator {σ : Type} (t : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) σ)
    (r : Fin k → ZMod q) (p : DecodeHelper m (k + l) q Unit) : Experiment := do
  let st ← (adv.query p.matrix p.cipher).run fun δ => do
    let s' ← ProbComp.uniform (Fin (k + l) → ZMod q)
    return p.cipher + p.matrix.mulVec s' + clampShift t δ
  adv.guess st r

/-- Key shift invariance of Theorem 1: for any fixed `A`, `s`, `w`, and shift `δ`, the shift
oracle's answer `A s_i + (w + δ')`, for a fresh uniform `s_i` and `δ' = clampShift t δ`, has the
same distribution as `(A s + w) + A s' + δ'` for a fresh uniform `s'`, since
`A (s + s') + (w + δ') = (A s + w) + A s' + δ'`. -/
private theorem eval_commonMatrix_query_eq
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (A : Matrix (Fin m) (Fin (k + l)) (ZMod q))
    (s : Fin (k + l) → ZMod q) (t : ℕ) (w δ : Fin m → ZMod q) :
    ProbComp.eval (weakReuseOracle (commonMatrixFuzzyExtractor m k l q decode) t A w δ) =
    ProbComp.eval (do
      let s' ← ProbComp.uniform (Fin (k + l) → ZMod q)
      return (A.mulVec s + w) + A.mulVec s' + clampShift t δ) := by
  simp only [weakReuseOracle, commonMatrixFuzzyExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [← Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft s)]
  congr 1 with s' : 1
  congr 1
  change A.mulVec (s + s') + (w + clampShift t δ) = A.mulVec s + w + A.mulVec s' + clampShift t δ
  rw [Matrix.mulVec_add]
  abel

/-- The query stage of `adv` has the same law against the honest shift oracle of
`commonMatrixFuzzyExtractor` as against the simulator's oracle. -/
private theorem eval_run_commonMatrix_query_eq {σ : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (A : Matrix (Fin m) (Fin (k + l)) (ZMod q))
    (s : Fin (k + l) → ZMod q) (t : ℕ) (w : Fin m → ZMod q)
    (program : ProbOracleComp (fun _ : Fin m → ZMod q => Fin m → ZMod q) σ) :
    ProbComp.eval (program.run
      (weakReuseOracle (commonMatrixFuzzyExtractor m k l q decode) t A w)) =
    ProbComp.eval (program.run fun δ => do
      let s' ← ProbComp.uniform (Fin (k + l) → ZMod q)
      return (A.mulVec s + w) + A.mulVec s' + clampShift t δ) := by
  simp only [ProbOracleComp.eval_run, eval_commonMatrix_query_eq decode A s t w]

/-- The weak-reusability real game of `commonMatrixFuzzyExtractor` (over a uniform public matrix
`A`) equals the single-enrollment `realGame` of `lweFuzzyExtractor` against
`commonMatrixSimulator t adv`. This is the real-game half of the reduction step in the proof of
[AponChoEldefrawyKatz2017], Theorem 1. -/
theorem weakReuseRealGame_commonMatrixFuzzyExtractor {σ : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) σ) :
    weakReuseRealGame (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t adv =
      (lweFuzzyExtractor m k l q decode).realGame W (commonMatrixSimulator t adv) := by
  simp only [weakReuseRealGame, FuzzyExtractor.realGame, Game.withSetup,
    weakReuseRealExperiment, FuzzyExtractor.realExperiment, lweFuzzyExtractor, decodeThenExtract,
    commonMatrixSimulator, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    Probability.PMF.uniformOfFintype_unit, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q))) W]
  congr 1 with w : 1
  congr 1 with A : 1
  simp only [commonMatrixFuzzyExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  congr 1 with s : 1
  rw [eval_run_commonMatrix_query_eq decode A s t w]

/-- The weak-reusability ideal game of `commonMatrixFuzzyExtractor` (over a uniform public matrix
`A`) equals the single-enrollment `idealGame` of `lweFuzzyExtractor` against
`commonMatrixSimulator t adv`. This is the ideal-game half of the reduction step in the proof of
[AponChoEldefrawyKatz2017], Theorem 1. -/
theorem weakReuseIdealGame_commonMatrixFuzzyExtractor {σ : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) σ) :
    weakReuseIdealGame (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t adv =
      (lweFuzzyExtractor m k l q decode).idealGame W (commonMatrixSimulator t adv) := by
  simp only [weakReuseIdealGame, FuzzyExtractor.idealGame, Game.withSetup,
    weakReuseIdealExperiment, FuzzyExtractor.idealExperiment, lweFuzzyExtractor, decodeThenExtract,
    commonMatrixSimulator, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    Probability.PMF.uniformOfFintype_unit, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q))) W]
  congr 1 with w : 1
  congr 1 with A : 1
  simp only [commonMatrixFuzzyExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  congr 1 with s : 1
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (Fin k → ZMod q))]
  rw [eval_run_commonMatrix_query_eq decode A s t w]

/-- The reduction step in the proof of [AponChoEldefrawyKatz2017], Theorem 1 (Section 3.3), as an
exact identity: for every source `W`, distance threshold `t` and weak-reusability adversary
`adv`, the weak-reusability advantage against `commonMatrixFuzzyExtractor` (under a uniform common
matrix `A`) equals the single-enrollment `securityAdvantage` of `lweFuzzyExtractor` against
`commonMatrixSimulator t adv`. This is a reduction lemma, not the security theorem: `adv` is
unrestricted, and no efficiency certificate for `commonMatrixSimulator` is given. -/
theorem weakReuseAdvantage_commonMatrixFuzzyExtractor_eq {σ : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) σ) :
    weakReuseAdvantage (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t adv =
      (lweFuzzyExtractor m k l q decode).securityAdvantage W (commonMatrixSimulator t adv) := by
  simp [weakReuseAdvantage, FuzzyExtractor.securityAdvantage,
    weakReuseRealGame_commonMatrixFuzzyExtractor, weakReuseIdealGame_commonMatrixFuzzyExtractor]

/-- Concrete reduction inequality for [AponChoEldefrawyKatz2017], Theorem 1, combining
`weakReuseAdvantage_commonMatrixFuzzyExtractor_eq` with `securityAdvantage_lweFuzzyExtractor_le`:
for every source `W`, distance threshold `t` and weak-reusability adversary `adv`, the
weak-reusability advantage against `commonMatrixFuzzyExtractor` is at most the sum of the
decisional LWE advantages (secret dimension `l`, error law `W`) of two explicit reductions built
from `adv`. This is not the security theorem: concluding weak reusability from
`DecisionLWEWithErrors` additionally needs an adversary class and efficiency certificates for
the reductions, which are future work. -/
theorem weakReuseAdvantage_commonMatrixFuzzyExtractor_le {σ : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) σ) :
    weakReuseAdvantage (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W
        (hardcoreKeyReduction (commonMatrixSimulator t adv)) +
      LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W
        (hardcoreUniformReduction (commonMatrixSimulator t adv)) := by
  rw [weakReuseAdvantage_commonMatrixFuzzyExtractor_eq]
  exact securityAdvantage_lweFuzzyExtractor_le decode W (commonMatrixSimulator t adv)

/-! ### Section 3.3 (p. 10): Non-strong-reusability of common-matrix FMR -/

omit [NeZero q] in
/-- Deterministic key recovery from one zero-shift enrollment in `commonMatrixFuzzyExtractor`
([AponChoEldefrawyKatz2017], Section 3.3, p. 10): if `c* = A s* + w*` and `c₁ = A s₁ + w*`
share the same matrix `A` and reading `w*`, then `c* - c₁ = A (s* - s₁)` has zero residual error,
and adding `r₁ = (s₁)_{1..k}` to the first `k` coordinates of `s* - s₁` recovers the challenge key
`r* = (s*)_{1..k}`. -/
theorem commonMatrix_recover_key_of_zero_shift
    (A : Matrix (Fin m) (Fin (k + l)) (ZMod q))
    (sStar s₁ : Fin (k + l) → ZMod q) (wStar : Fin m → ZMod q) :
    (A.mulVec sStar + wStar) - (A.mulVec s₁ + wStar) = A.mulVec (sStar - s₁) ∧
      (fun i => (sStar - s₁) (Fin.castAdd l i)) + (fun i => s₁ (Fin.castAdd l i)) =
        fun i => sStar (Fin.castAdd l i) := by
  constructor
  · rw [add_sub_add_right_eq_sub, ← Matrix.mulVec_sub]
  · ext i
    simp

/-- The 1-query strong-reusability attacker against `commonMatrixFuzzyExtractor`
([AponChoEldefrawyKatz2017], Section 3.3, p. 10): it queries shift `δ = 0`, receives
`(c₁, r₁)`, runs `decode A (c* - c₁)` to recover `Δs = s* - s₁`, saves the candidate key
`(Δs)_{1..k} + r₁` (or `0` if decoding fails), and checks whether the challenge key equals it. -/
noncomputable def commonMatrixStrongAttack
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))) :
    StrongReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) (Fin k → ZMod q) where
  query A cStar := do
    let (c₁, r₁) ← ProbOracleComp.query 0
    let sOpt ← ProbOracleComp.sample (decode A (cStar - c₁))
    return match sOpt with
      | some ds => (fun i => ds (Fin.castAdd l i)) + r₁
      | none => 0
  guess recovered r := return decide (r = recovered)

/-- If `decode` fails with probability at most `δ` on error `0` over a uniform matrix
(`DecoderCorrectWithError decode 0 δ`), then the 1-query attack `commonMatrixStrongAttack decode`
outputs `false` in the real strong-reusability game against `commonMatrixFuzzyExtractor` (uniform
common matrix) with probability at most `δ`, for every source `W`. -/
theorem failProbability_strongReuseRealGame_commonMatrixStrongAttack_le
    {decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))}
    {δ : ℝ≥0} (hdec : DecoderCorrectWithError decode 0 δ)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) :
    Game.failProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode)) ≤ δ := by
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [strongReuseRealGame, Game.withSetup, strongReuseRealExperiment,
    commonMatrixFuzzyExtractor, commonMatrixStrongAttack, strongReuseOracle,
    ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbOracleComp.run_sample,
    ProbOracleComp.run_pure, clampShift_zero, add_zero, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q))) W]
  refine PMF.bind_apply_le_on_support _ fun w _ => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (PMF.uniformOfFintype (Fin (k + l) → ZMod q))]
  refine PMF.bind_apply_le_on_support _ fun sStar _ => ?_
  rw [PMF.bind_comm (PMF.uniformOfFintype (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (PMF.uniformOfFintype (Fin (k + l) → ZMod q))]
  refine PMF.bind_apply_le_on_support _ fun s₁ _ => ?_
  have hsub : ∀ A : Matrix (Fin m) (Fin (k + l)) (ZMod q),
      (A.mulVec sStar + w) - (A.mulVec s₁ + w) = A.mulVec (sStar - s₁) + 0 := fun A => by
    rw [add_zero, (commonMatrix_recover_key_of_zero_shift A sStar s₁ w).1]
  simp only [hsub]
  refine uniform_bind_decode_bind_apply_false_le_of_failProbability_le decode (sStar - s₁) 0 _
    (fun A => ?_) (hdec (sStar - s₁) 0 (by simp))
  simp only [(commonMatrix_recover_key_of_zero_shift A sStar s₁ w).2, decide_true]

private theorem uniform_bind_decide_eq (x : Fin k → ZMod q) :
    ((PMF.uniformOfFintype (Fin k → ZMod q)).bind fun u => PMF.pure (decide (u = x))) =
      (PMF.uniformOfFintype (Fin k → ZMod q)).bind fun u => PMF.pure (decide (u = 0)) := by
  rw [← Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addRight x)
    (fun u => PMF.pure (decide (u = x)))]
  simp

private theorem uniform_bind_decide_zero_apply_true :
    ((PMF.uniformOfFintype (Fin k → ZMod q)).bind fun u => PMF.pure (decide (u = 0))) true =
      ((q : ℝ≥0∞) ^ k)⁻¹ := by
  simp [PMF.bind_apply, PMF.uniformOfFintype_apply, PMF.pure_apply, tsum_fintype,
    ZMod.card]

/-- In the ideal strong-reusability game against `commonMatrixFuzzyExtractor`, the attack
`commonMatrixStrongAttack decode` outputs `true` with probability exactly `1 / q ^ k`: the uniform
key `u` is independent of the attacker's recovered key. This holds for every setup program and
every source `W`. -/
theorem strongReuseIdealGame_commonMatrixStrongAttack_apply_true
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (setup : ProbComp (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t : ℕ) :
    strongReuseIdealGame setup (commonMatrixFuzzyExtractor m k l q decode) W t
      (commonMatrixStrongAttack decode) true = ((q : ℝ≥0∞) ^ k)⁻¹ := by
  simp only [strongReuseIdealGame, Game.withSetup, strongReuseIdealExperiment,
    commonMatrixFuzzyExtractor, commonMatrixStrongAttack, strongReuseOracle,
    ProbOracleComp.run_bind, ProbOracleComp.run_query, ProbOracleComp.run_sample,
    ProbOracleComp.run_pure, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind, uniform_bind_decide_eq, PMF.bind_const]
  exact uniform_bind_decide_zero_apply_true

/-- The Section 3.3 attack as an advantage lower bound ([AponChoEldefrawyKatz2017], p. 10): if
`decode` fails with probability at most `δ` on error `0` over a uniform matrix, then the 1-query
attack `commonMatrixStrongAttack decode` has strong-reusability advantage at least
`1 - δ - 1 / q ^ k` against `commonMatrixFuzzyExtractor`, for every source `W`. So the scheme is not
strongly reusable whenever the decoder works and `q ^ k` is large. -/
theorem strongReuseAdvantage_commonMatrixStrongAttack_ge
    {decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))}
    {δ : ℝ≥0} (hdec : DecoderCorrectWithError decode 0 δ)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) :
    1 - (δ : ℝ) - 1 / (q : ℝ) ^ k ≤
      strongReuseAdvantage (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
        (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode) := by
  have hfail := failProbability_strongReuseRealGame_commonMatrixStrongAttack_le hdec W t
  have hsum := Game.succProbability_add_failProbability (strongReuseRealGame
    (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode))
  have hideal : (Game.succProbability (strongReuseIdealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode)) : ℝ) =
      1 / (q : ℝ) ^ k := by
    rw [Game.coe_succProbability, strongReuseIdealGame_commonMatrixStrongAttack_apply_true]
    simp [ENNReal.toReal_inv]
  rw [strongReuseAdvantage, Game.coe_advantage, hideal]
  have hsumR : (Game.succProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode)) : ℝ) +
      (Game.failProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode)) : ℝ) =
      1 := by exact_mod_cast hsum
  have hfailR : (Game.failProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t (commonMatrixStrongAttack decode)) : ℝ) ≤
      δ := by exact_mod_cast hfail
  exact le_trans (by linarith) (le_abs_self _)

end CommonMatrix

end Cslib.Crypto.FuzzyExtractor
