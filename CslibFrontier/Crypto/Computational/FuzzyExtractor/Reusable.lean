/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract
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
* An adaptive `Q`-query adversary (`ReuseAdversary`) with generic state `St` receives `(pp, p*)`
  from the challenge enrollment `(r*, p*) ← (fe pp).gen w*`, adaptively chooses `Q` shifts
  `δ_i : Fin m → ZMod q` (enforced to satisfy `hammingNorm δ_i ≤ t` via `clampShift t`, which
  replaces out-of-range shifts by `0`; adversaries making fewer than `Q` queries pad with dummy
  zero shifts), and receives a leakage value from a fresh enrollment `(r_i, p_i) ← (fe pp).gen
  (w* + δ_i)` on each query. The challenge key (real or uniform) is given only after the queries,
  as in step 3 of Definitions 2 and 3.
* In *weak reusability* (Definition 2), the leakage on each shift query is the helper `p_i` alone
  (`Leak = Helper`).
* In *strong reusability* (Definition 3), the leakage on each shift query is both the helper and
  the extracted key `(p_i, r_i)` (`Leak = Helper × Key`).
* Advantages (`weakReuseAdvantage`, `strongReuseAdvantage`) are defined as
  `Game.advantage realGame idealGame = |Pr[real] - Pr[ideal]|`, which is equivalent up to a factor
  of `2` to the paper's `1/2 + ε` guessing-game formulation.

This file defines the experiments and advantages only. It does not define a security predicate
"`fe` is reusable": such a predicate needs a class of efficient adversaries, which is future work.

In Section 3.3 ([AponChoEldefrawyKatz2017], Theorem 1), Apon et al. modify the Fuller–Meng–Reyzin
construction (`lweFuzzyExtractor`) by placing the random matrix `A ∈ Z_q^{m × (k + l)}` into the
common public parameters so that `Gen` samples only the secret `s` and outputs `c = A s + w`. We
formalize this construction as `commonMatrixFuzzyExtractor` and prove the reduction step of the
proof of Theorem 1 as an exact identity: for every source `W`, threshold `t`, query count `Q`, and
weak-reuse adversary `adv`, the `Q`-query weak-reuse advantage equals the single-enrollment
`securityAdvantage` of `lweFuzzyExtractor` against an explicit simulator
`commonMatrixSimulator t Q adv` that answers each shift `δ` with `c* + A s' + δ` for a fresh
uniform secret `s'`. Combining this identity with `securityAdvantage_lweFuzzyExtractor_le` bounds
the weak-reuse advantage of each adversary by two decisional LWE advantages of explicit
reductions. These are concrete reduction lemmas, not the security theorem itself.

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
  `Cslib.Crypto.FuzzyExtractor.StrongReuseAdversary`: adaptive `Q`-query reusability adversaries
  with generic state `St`.
* `Cslib.Crypto.FuzzyExtractor.clampShift`, `Cslib.Crypto.FuzzyExtractor.reuseQueryLoop`: Hamming
  weight enforcement (`hammingNorm δ ≤ t`) and the `Q`-step adaptive shift-query loop.
* `Cslib.Crypto.FuzzyExtractor.weakReuseRealGame`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseIdealGame`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage`: the experiment of Definition 2.
* `Cslib.Crypto.FuzzyExtractor.strongReuseRealGame`,
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

* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_eq_strongReuseAdvantage_toStrong`: a weak-reuse
  adversary has the same advantage as its key-ignoring strong-reuse embedding.
* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_zero_eq_securityAdvantage`,
  `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_ofDistinguisher_eq_securityAdvantage`: the weak
  reuse experiment with `Q = 0` queries coincides with the basic fuzzy-extractor experiment
  (Section 2.2 remark).
* `Cslib.Crypto.FuzzyExtractor.DecoderCorrectWithError.setupCorrect_commonMatrixFuzzyExtractor`:
  `δ`-error reproduction correctness of `commonMatrixFuzzyExtractor` over a uniform matrix.
* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_eq`: the reduction
  step of Theorem 1 as an exact advantage identity.
* `Cslib.Crypto.FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_le`: the `Q`-query
  weak-reuse advantage of each adversary is at most two decisional LWE advantages of explicit
  reductions.
* `Cslib.Crypto.FuzzyExtractor.strongReuseAdvantage_commonMatrixStrongAttack_ge`: the Section 3.3
  attack has strong-reuse advantage at least `1 - δ - 1 / q ^ k`.

## What is not proved

* A reusability security theorem. Here the adversary is any `ReuseAdversary`, with no efficiency
  bound. Concluding reusability from `DecisionLWEWithErrors` needs an adversary class in the
  reuse experiments and efficiency certificates for `commonMatrixSimulator` and the reductions;
  this is future work, recorded under "Reusable fuzzy extractors from LWE" in
  `roadmap/cryptography.md`.
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

/-! ### Adaptive shift-query adversaries and query loop (Sections 2.1–2.2) -/

/-- An adaptive reusability adversary with state type `St` against a public-parameter fuzzy
extractor over `Fin m → ZMod q` ([AponChoEldefrawyKatz2017], Definitions 2 and 3):
* `start pp p*` initializes the adversary's state from the public parameter `pp` and the challenge
  helper string `p*`;
* `shift st` outputs the updated state and the next shift query `δ : Fin m → ZMod q`;
* `observe st leak` absorbs the oracle response `leak` (either `Helper` in weak reusability or
  `Helper × Key` in strong reusability);
* `guess st r` outputs a Boolean guess given the final state and challenge key candidate `r`. -/
structure ReuseAdversary (PP : Type) (m q : ℕ) (Key Helper Leak St : Type) where
  /-- Initialize state from the public parameter and challenge helper string. -/
  start : PP → Helper → ProbComp St
  /-- Choose the next shift vector `δ : Fin m → ZMod q`. -/
  shift : St → ProbComp (St × (Fin m → ZMod q))
  /-- Absorb the leakage from the shifted enrollment. -/
  observe : St → Leak → ProbComp St
  /-- Distinguish the real key `r*` from a uniform key `u`. -/
  guess : St → Key → ProbComp Bool

/-- A weak-reusability adversary (Definition 2): each shift query leaks only the helper string
`p_i : Helper`. -/
abbrev WeakReuseAdversary (PP : Type) (m q : ℕ) (Key Helper St : Type) : Type :=
  ReuseAdversary PP m q Key Helper Helper St

/-- A strong-reusability adversary (Definition 3): each shift query leaks both the helper string
and the extracted key `(p_i, r_i) : Helper × Key`. -/
abbrev StrongReuseAdversary (PP : Type) (m q : ℕ) (Key Helper St : Type) : Type :=
  ReuseAdversary PP m q Key Helper (Helper × Key) St

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

/-- Run `Q` adaptive shift queries of `adv` against `oracle`, clamping each queried shift `δ` to
Hamming weight at most `t` via `clampShift t`. Adversaries that make fewer than `Q` queries can
pad with dummy `0` shifts. -/
@[expose] def reuseQueryLoop {PP : Type} {m q : ℕ} {Key Helper Leak St : Type}
    (t : ℕ) (oracle : (Fin m → ZMod q) → ProbComp Leak)
    (adv : ReuseAdversary PP m q Key Helper Leak St) : ℕ → St → ProbComp St
  | 0, st => return st
  | Q + 1, st => do
    let (st', δ) ← adv.shift st
    let leak ← oracle (clampShift t δ)
    let st'' ← adv.observe st' leak
    reuseQueryLoop t oracle adv Q st''

/-- Two shift oracles with the same output distribution at every valid shift induce the same output
distribution in `reuseQueryLoop`. -/
theorem eval_reuseQueryLoop_congr {PP : Type} {m q : ℕ} {Key Helper Leak St : Type}
    (t : ℕ) {oracle₁ oracle₂ : (Fin m → ZMod q) → ProbComp Leak}
    (adv : ReuseAdversary PP m q Key Helper Leak St)
    (horacle : ∀ δ, hammingNorm δ ≤ t → ProbComp.eval (oracle₁ δ) = ProbComp.eval (oracle₂ δ))
    (Q : ℕ) (st : St) :
    ProbComp.eval (reuseQueryLoop t oracle₁ adv Q st) =
      ProbComp.eval (reuseQueryLoop t oracle₂ adv Q st) := by
  induction Q generalizing st with
  | zero => rfl
  | succ Q ih =>
    simp only [reuseQueryLoop, ProbComp.eval_bind]
    congr 1 with ⟨st', δ⟩ : 1
    rw [horacle (clampShift t δ) (hammingNorm_clampShift_le t δ)]
    congr 1 with leak : 1
    congr 1 with st'' : 1
    exact ih st''

/-! ### Definition 2: Weak reusability -/

section WeakReuse

variable {PP : Type} {m q : ℕ} {Key Helper St : Type}

/-- The real weak-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 2): sample `(r*, p*) ← (fe pp).gen w*`, answer `Q` shift
queries `δ_i` with helper strings `p_i` from fresh runs of `(fe pp).gen (w* + clampShift t δ_i)`,
and pass `r*` to `adv.guess`. -/
@[expose] def weakReuseRealExperiment (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t Q : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : WeakReuseAdversary PP m q Key Helper St) : Experiment := do
  let (rStar, pStar) ← (fe pp).gen w
  let st₀ ← adv.start pp pStar
  let st ← reuseQueryLoop t (fun δ => do
    let (_, p) ← (fe pp).gen (w + δ)
    return p) adv Q st₀
  adv.guess st rStar

/-- The ideal weak-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 2): as `weakReuseRealExperiment`, except `adv.guess`
receives an independent uniform key `u ← ProbComp.uniform Key` in place of `r*`. -/
@[expose] noncomputable def weakReuseIdealExperiment [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t Q : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : WeakReuseAdversary PP m q Key Helper St) : Experiment := do
  let (_, pStar) ← (fe pp).gen w
  let st₀ ← adv.start pp pStar
  let st ← reuseQueryLoop t (fun δ => do
    let (_, p) ← (fe pp).gen (w + δ)
    return p) adv Q st₀
  let u ← ProbComp.uniform Key
  adv.guess st u

/-- The real weak-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 2). -/
@[expose] noncomputable def weakReuseRealGame (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    weakReuseRealExperiment fe t Q pp w adv

/-- The ideal weak-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 2). -/
@[expose] noncomputable def weakReuseIdealGame [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    weakReuseIdealExperiment fe t Q pp w adv

/-- The weak-reusability distinguishing advantage of `adv` on source `W` with `Q` shift queries of
Hamming weight at most `t` ([AponChoEldefrawyKatz2017], Definition 2). -/
noncomputable abbrev weakReuseAdvantage [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) : ℝ≥0 :=
  Game.advantage (weakReuseRealGame setup fe W t Q adv) (weakReuseIdealGame setup fe W t Q adv)

end WeakReuse

/-! ### Definition 3: Strong reusability -/

section StrongReuse

variable {PP : Type} {m q : ℕ} {Key Helper St : Type}

/-- The real strong-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 3): sample `(r*, p*) ← (fe pp).gen w*`, answer `Q` shift
queries `δ_i` with both `(p_i, r_i)` from fresh runs of `(fe pp).gen (w* + clampShift t δ_i)`,
and pass `r*` to `adv.guess`. -/
@[expose] def strongReuseRealExperiment (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t Q : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : StrongReuseAdversary PP m q Key Helper St) : Experiment := do
  let (rStar, pStar) ← (fe pp).gen w
  let st₀ ← adv.start pp pStar
  let st ← reuseQueryLoop t (fun δ => do
    let (r, p) ← (fe pp).gen (w + δ)
    return (p, r)) adv Q st₀
  adv.guess st rStar

/-- The ideal strong-reusability experiment on fixed public parameter `pp` and source reading `w*`
([AponChoEldefrawyKatz2017], Definition 3): as `strongReuseRealExperiment`, except `adv.guess`
receives an independent uniform key `u ← ProbComp.uniform Key` in place of `r*`. -/
@[expose] noncomputable def strongReuseIdealExperiment [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t Q : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : StrongReuseAdversary PP m q Key Helper St) : Experiment := do
  let (_, pStar) ← (fe pp).gen w
  let st₀ ← adv.start pp pStar
  let st ← reuseQueryLoop t (fun δ => do
    let (r, p) ← (fe pp).gen (w + δ)
    return (p, r)) adv Q st₀
  let u ← ProbComp.uniform Key
  adv.guess st u

/-- The real strong-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 3). -/
@[expose] noncomputable def strongReuseRealGame (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper St) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    strongReuseRealExperiment fe t Q pp w adv

/-- The ideal strong-reusability game over setup law `setup` and source `W`, built with
`Game.withSetup W` ([AponChoEldefrawyKatz2017], Definition 3). -/
@[expose] noncomputable def strongReuseIdealGame [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper St) : Game :=
  (ProbComp.eval setup).bind fun pp => Game.withSetup W fun w =>
    strongReuseIdealExperiment fe t Q pp w adv

/-- The strong-reusability distinguishing advantage of `adv` on source `W` with `Q` shift queries
of Hamming weight at most `t` ([AponChoEldefrawyKatz2017], Definition 3). -/
noncomputable abbrev strongReuseAdvantage [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : StrongReuseAdversary PP m q Key Helper St) : ℝ≥0 :=
  Game.advantage (strongReuseRealGame setup fe W t Q adv)
    (strongReuseIdealGame setup fe W t Q adv)

end StrongReuse

/-! ### Relations between strong reusability, weak reusability, and basic security -/

section Relations

variable {PP : Type} {m q : ℕ} {Key Helper St : Type}

/-- View a weak-reusability adversary as a strong-reusability adversary that ignores the leaked key
component on each shift query. -/
def WeakReuseAdversary.toStrong (adv : WeakReuseAdversary PP m q Key Helper St) :
    StrongReuseAdversary PP m q Key Helper St where
  start := adv.start
  shift := adv.shift
  observe st leak :=
    let (p, _) := leak
    adv.observe st p
  guess := adv.guess

private theorem eval_reuseQueryLoop_toStrong
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (t : ℕ) (pp : PP) (w : Fin m → ZMod q)
    (adv : WeakReuseAdversary PP m q Key Helper St) (Q : ℕ) (st : St) :
    ProbComp.eval (reuseQueryLoop t (fun δ => do
      let (r, p) ← (fe pp).gen (w + δ)
      return (p, r)) adv.toStrong Q st) =
    ProbComp.eval (reuseQueryLoop t (fun δ => do
      let (_, p) ← (fe pp).gen (w + δ)
      return p) adv Q st) := by
  induction Q generalizing st with
  | zero => rfl
  | succ Q ih =>
    simp only [reuseQueryLoop, WeakReuseAdversary.toStrong, ProbComp.eval_bind, ProbComp.eval_pure,
      PMF.bind_bind, PMF.pure_bind]
    congr 1 with ⟨st', δ⟩ : 1
    congr 1 with ⟨r, p⟩ : 1
    congr 1 with st'' : 1
    exact ih st''

/-- The strong-reusability real game on `adv.toStrong` equals the weak-reusability real game on
`adv`. -/
@[simp] theorem strongReuseRealGame_toStrong (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    strongReuseRealGame setup fe W t Q adv.toStrong =
      weakReuseRealGame setup fe W t Q adv := by
  simp only [strongReuseRealGame, weakReuseRealGame, Game.withSetup,
    strongReuseRealExperiment, weakReuseRealExperiment, ProbComp.eval_bind]
  congr 1 with pp : 1
  congr 1 with w : 1
  congr 1 with ⟨rStar, pStar⟩ : 1
  change ((adv.start pp pStar).eval.bind _) = _
  congr 1 with st₀ : 1
  rw [eval_reuseQueryLoop_toStrong]
  rfl

/-- The strong-reusability ideal game on `adv.toStrong` equals the weak-reusability ideal game on
`adv`. -/
@[simp] theorem strongReuseIdealGame_toStrong [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    strongReuseIdealGame setup fe W t Q adv.toStrong =
      weakReuseIdealGame setup fe W t Q adv := by
  simp only [strongReuseIdealGame, weakReuseIdealGame, Game.withSetup,
    strongReuseIdealExperiment, weakReuseIdealExperiment, ProbComp.eval_bind]
  congr 1 with pp : 1
  congr 1 with w : 1
  congr 1 with ⟨rStar, pStar⟩ : 1
  change ((adv.start pp pStar).eval.bind _) = _
  congr 1 with st₀ : 1
  rw [eval_reuseQueryLoop_toStrong]
  rfl

/-- Every weak-reusability adversary achieves the exact same advantage when embedded as a
key-ignoring strong-reusability adversary. -/
theorem weakReuseAdvantage_eq_strongReuseAdvantage_toStrong [Fintype Key] [Nonempty Key]
    (setup : ProbComp PP) (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    weakReuseAdvantage setup fe W t Q adv =
      strongReuseAdvantage setup fe W t Q adv.toStrong := by
  simp [weakReuseAdvantage, strongReuseAdvantage]

/-- Convert a weak-reusability adversary at a fixed public parameter `pp` into a single-enrollment
fuzzy-extractor distinguisher (`Q = 0`). -/
def WeakReuseAdversary.toDistinguisher (adv : WeakReuseAdversary PP m q Key Helper St)
    (pp : PP) (r : Key) (p : Helper) : Experiment := do
  let st₀ ← adv.start pp p
  adv.guess st₀ r

/-- Embed a single-enrollment distinguisher `D : Key → Helper → Experiment` as a weak-reusability
adversary whose state records the challenge helper string `p*`. -/
def WeakReuseAdversary.ofDistinguisher (D : Key → Helper → Experiment) :
    WeakReuseAdversary PP m q Key Helper Helper where
  start _ pStar := return pStar
  shift st := return (st, 0)
  observe st _ := return st
  guess pStar r := D r pStar

/-- With `Q = 0` queries at the point setup `pure pp`, the weak-reusability real game equals
the basic fuzzy-extractor `realGame` for `adv.toDistinguisher pp`. -/
theorem weakReuseRealGame_zero (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) (pp : PP)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    weakReuseRealGame (pure pp) fe W t 0 adv =
      (fe pp).realGame W (adv.toDistinguisher pp) := by
  simp [weakReuseRealGame, FuzzyExtractor.realGame, Game.withSetup, weakReuseRealExperiment,
    FuzzyExtractor.realExperiment, reuseQueryLoop, WeakReuseAdversary.toDistinguisher,
    ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]

/-- With `Q = 0` queries at the point setup `pure pp`, the weak-reusability ideal game equals
the basic fuzzy-extractor `idealGame` for `adv.toDistinguisher pp`. -/
theorem weakReuseIdealGame_zero [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) (pp : PP)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    weakReuseIdealGame (pure pp) fe W t 0 adv =
      (fe pp).idealGame W (adv.toDistinguisher pp) := by
  simp only [weakReuseIdealGame, FuzzyExtractor.idealGame, Game.withSetup,
    weakReuseIdealExperiment, FuzzyExtractor.idealExperiment, reuseQueryLoop,
    WeakReuseAdversary.toDistinguisher, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.pure_bind]
  congr 1 with w : 1
  congr 1 with ⟨rStar, pStar⟩ : 1
  rw [PMF.bind_comm]

/-- Weak-reusability advantage with `Q = 0` queries at the point setup `pure pp` equals the basic
fuzzy-extractor `securityAdvantage` ([AponChoEldefrawyKatz2017], Section 2.2 remark). -/
theorem weakReuseAdvantage_zero_eq_securityAdvantage [Fintype Key] [Nonempty Key]
    (fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) (pp : PP)
    (adv : WeakReuseAdversary PP m q Key Helper St) :
    weakReuseAdvantage (pure pp) fe W t 0 adv =
      (fe pp).securityAdvantage W (adv.toDistinguisher pp) := by
  simp [weakReuseAdvantage, FuzzyExtractor.securityAdvantage, weakReuseRealGame_zero,
    weakReuseIdealGame_zero]

/-- Conversely, for a parameter-independent fuzzy extractor `fe₀` and any setup law `setup`, the
`Q = 0` weak-reusability advantage of `WeakReuseAdversary.ofDistinguisher D` equals
`fe₀.securityAdvantage W D`. -/
@[simp] theorem weakReuseAdvantage_ofDistinguisher_eq_securityAdvantage
    [Fintype Key] [Nonempty Key] (setup : ProbComp PP)
    (fe₀ : FuzzyExtractor (Fin m → ZMod q) Key Helper)
    (W : PMF (Fin m → ZMod q)) (t : ℕ) (D : Key → Helper → Experiment) :
    weakReuseAdvantage setup (fun _ => fe₀) W t 0 (WeakReuseAdversary.ofDistinguisher D) =
      fe₀.securityAdvantage W D := by
  have hreal : weakReuseRealGame setup (fun _ => fe₀) W t 0
      (WeakReuseAdversary.ofDistinguisher D) = fe₀.realGame W D := by
    simp [weakReuseRealGame, FuzzyExtractor.realGame, Game.withSetup, weakReuseRealExperiment,
      FuzzyExtractor.realExperiment, reuseQueryLoop, WeakReuseAdversary.ofDistinguisher,
      ProbComp.eval_bind, PMF.bind_const]
  have hideal : weakReuseIdealGame setup (fun _ => fe₀) W t 0
      (WeakReuseAdversary.ofDistinguisher D) = fe₀.idealGame W D := by
    simp [weakReuseIdealGame, FuzzyExtractor.idealGame, Game.withSetup, weakReuseIdealExperiment,
      FuzzyExtractor.idealExperiment, reuseQueryLoop, WeakReuseAdversary.ofDistinguisher,
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
`p = ⟨A, c*, ()⟩`, it runs `adv` with public matrix `A` and challenge helper `c*`, answering each
clamped shift query `δ` by sampling a fresh uniform `s' : Fin (k + l) → ZMod q` and returning
`c* + A s' + δ`. The simulator never sees the secret `s` or reading `w*`. -/
noncomputable def commonMatrixSimulator {St : Type} (t Q : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) St)
    (r : Fin k → ZMod q) (p : DecodeHelper m (k + l) q Unit) : Experiment := do
  let st₀ ← adv.start p.matrix p.cipher
  let st ← reuseQueryLoop t (fun δ => do
    let s' ← ProbComp.uniform (Fin (k + l) → ZMod q)
    return p.cipher + p.matrix.mulVec s' + δ) adv Q st₀
  adv.guess st r

/-- Key shift invariance of Theorem 1: for any fixed `A`, `s`, `w`, and shift `δ`, sampling a fresh
uniform `s_i` and forming `A s_i + (w + δ)` has the exact same distribution as sampling a fresh
uniform `s'` and forming `(A s + w) + A s' + δ = A (s + s') + (w + δ)`. -/
private theorem eval_commonMatrix_query_eq
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (A : Matrix (Fin m) (Fin (k + l)) (ZMod q))
    (s : Fin (k + l) → ZMod q) (w δ : Fin m → ZMod q) :
    ProbComp.eval (do
      let (_, p) ← (commonMatrixFuzzyExtractor m k l q decode A).gen (w + δ)
      return p) =
    ProbComp.eval (do
      let s' ← ProbComp.uniform (Fin (k + l) → ZMod q)
      return (A.mulVec s + w) + A.mulVec s' + δ) := by
  simp only [commonMatrixFuzzyExtractor, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [← Probability.PMF.uniformOfFintype_bind_equiv (Equiv.addLeft s)]
  congr 1 with s' : 1
  congr 1
  change A.mulVec (s + s') + (w + δ) = A.mulVec s + w + A.mulVec s' + δ
  rw [Matrix.mulVec_add]
  abel

/-- The `Q`-query weak-reusability real game of `commonMatrixFuzzyExtractor` (over a uniform public
matrix `A`) equals the single-enrollment `realGame` of `lweFuzzyExtractor` against
`commonMatrixSimulator t Q adv`. This is the real-game half of the reduction step in the proof of
[AponChoEldefrawyKatz2017], Theorem 1. -/
theorem weakReuseRealGame_commonMatrixFuzzyExtractor {St : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) St) :
    weakReuseRealGame (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t Q adv =
      (lweFuzzyExtractor m k l q decode).realGame W (commonMatrixSimulator t Q adv) := by
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
  congr 1 with st₀ : 1
  rw [← eval_reuseQueryLoop_congr t adv
    (fun δ _ => eval_commonMatrix_query_eq decode A s w δ) Q st₀]
  rfl

/-- The `Q`-query weak-reusability ideal game of `commonMatrixFuzzyExtractor` (over a uniform
public matrix `A`) equals the single-enrollment `idealGame` of `lweFuzzyExtractor` against
`commonMatrixSimulator t Q adv`. This is the ideal-game half of the reduction step in the proof
of [AponChoEldefrawyKatz2017], Theorem 1. -/
theorem weakReuseIdealGame_commonMatrixFuzzyExtractor {St : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) St) :
    weakReuseIdealGame (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t Q adv =
      (lweFuzzyExtractor m k l q decode).idealGame W (commonMatrixSimulator t Q adv) := by
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
  congr 1 with st₀ : 1
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (Fin k → ZMod q))]
  rw [← eval_reuseQueryLoop_congr t adv
    (fun δ _ => eval_commonMatrix_query_eq decode A s w δ) Q st₀]
  rfl

/-- The reduction step in the proof of [AponChoEldefrawyKatz2017], Theorem 1 (Section 3.3), as an
exact identity: for every source `W`, distance threshold `t`, query count `Q`, and
weak-reusability adversary `adv`, the `Q`-query weak-reusability advantage against
`commonMatrixFuzzyExtractor` (under a uniform common matrix `A`) equals the single-enrollment
`securityAdvantage` of `lweFuzzyExtractor` against `commonMatrixSimulator t Q adv`. This is a
reduction lemma, not the security theorem: `adv` is unrestricted, and no efficiency certificate
for `commonMatrixSimulator` is given. -/
theorem weakReuseAdvantage_commonMatrixFuzzyExtractor_eq {St : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) St) :
    weakReuseAdvantage (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t Q adv =
      (lweFuzzyExtractor m k l q decode).securityAdvantage W (commonMatrixSimulator t Q adv) := by
  simp [weakReuseAdvantage, FuzzyExtractor.securityAdvantage,
    weakReuseRealGame_commonMatrixFuzzyExtractor, weakReuseIdealGame_commonMatrixFuzzyExtractor]

/-- Concrete reduction inequality for [AponChoEldefrawyKatz2017], Theorem 1, combining
`weakReuseAdvantage_commonMatrixFuzzyExtractor_eq` with `securityAdvantage_lweFuzzyExtractor_le`:
for every source `W`, distance threshold `t`, query count `Q`, and weak-reusability adversary
`adv`, the `Q`-query weak-reusability advantage against `commonMatrixFuzzyExtractor` is at most the
sum of the decisional LWE advantages (secret dimension `l`, error law `W`) of two explicit
reductions built from `adv`. This is not the security theorem: concluding weak reusability from
`DecisionLWEWithErrors` additionally needs an adversary class and efficiency certificates for
the reductions, which are future work. -/
theorem weakReuseAdvantage_commonMatrixFuzzyExtractor_le {St : Type}
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q)))
    (W : PMF (Fin m → ZMod q)) (t Q : ℕ)
    (adv : WeakReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) St) :
    weakReuseAdvantage (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t Q adv ≤
      LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W
        (hardcoreKeyReduction (commonMatrixSimulator t Q adv)) +
      LWE.advantage (PMF.uniformOfFintype (Fin l → ZMod q)) W
        (hardcoreUniformReduction (commonMatrixSimulator t Q adv)) := by
  rw [weakReuseAdvantage_commonMatrixFuzzyExtractor_eq]
  exact securityAdvantage_lweFuzzyExtractor_le decode W (commonMatrixSimulator t Q adv)

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

/-- State of the 1-query strong-reusability attack `commonMatrixStrongAttack` on
`commonMatrixFuzzyExtractor`. -/
structure CommonMatrixAttackState (m k l q : ℕ) where
  /-- The public matrix `A`. -/
  matrix : Matrix (Fin m) (Fin (k + l)) (ZMod q)
  /-- The challenge helper `c* = A s* + w*`. -/
  cipherStar : Fin m → ZMod q
  /-- The candidate key recovered after observing `(c₁, r₁)` on the first shift query. -/
  recoveredKey : Fin k → ZMod q

/-- The 1-query strong-reusability attacker against `commonMatrixFuzzyExtractor`
([AponChoEldefrawyKatz2017], Section 3.3, p. 10): it queries shift `δ = 0`, receives
`(c₁, r₁)`, runs `decode A (c* - c₁)` to recover `Δs = s* - s₁`, sets its candidate key to
`(Δs)_{1..k} + r₁`, and checks whether the challenge key equals this recovered key. -/
noncomputable def commonMatrixStrongAttack
    (decode : Matrix (Fin m) (Fin (k + l)) (ZMod q) → (Fin m → ZMod q) →
      ProbComp (Option (Fin (k + l) → ZMod q))) :
    StrongReuseAdversary (Matrix (Fin m) (Fin (k + l)) (ZMod q)) m q
      (Fin k → ZMod q) (Fin m → ZMod q) (CommonMatrixAttackState m k l q) where
  start A cStar := return ⟨A, cStar, 0⟩
  shift st := return (st, 0)
  observe st leak := do
    let (c₁, r₁) := leak
    let sOpt ← decode st.matrix (st.cipherStar - c₁)
    match sOpt with
    | some ds =>
      return ⟨st.matrix, st.cipherStar, (fun i => ds (Fin.castAdd l i)) + r₁⟩
    | none =>
      return st
  guess st r := return decide (r = st.recoveredKey)

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
      (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode)) ≤ δ := by
  rw [← ENNReal.coe_le_coe]
  simp only [Game.failProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  simp only [strongReuseRealGame, Game.withSetup, strongReuseRealExperiment,
    commonMatrixFuzzyExtractor, commonMatrixStrongAttack, reuseQueryLoop, clampShift_zero,
    add_zero, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
    PMF.bind_bind, PMF.pure_bind]
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
  simp only [ProbComp.eval_pure, PMF.pure_bind]
  rw [(commonMatrix_recover_key_of_zero_shift A sStar s₁ w).2]
  simp

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
    strongReuseIdealGame setup (commonMatrixFuzzyExtractor m k l q decode) W t 1
      (commonMatrixStrongAttack decode) true = ((q : ℝ≥0∞) ^ k)⁻¹ := by
  simp only [strongReuseIdealGame, Game.withSetup, strongReuseIdealExperiment,
    commonMatrixFuzzyExtractor, commonMatrixStrongAttack, reuseQueryLoop,
    ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform,
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
        (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode) := by
  have hfail := failProbability_strongReuseRealGame_commonMatrixStrongAttack_le hdec W t
  have hsum := Game.succProbability_add_failProbability (strongReuseRealGame
    (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
    (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode))
  have hideal : (Game.succProbability (strongReuseIdealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode)) : ℝ) =
      1 / (q : ℝ) ^ k := by
    rw [Game.coe_succProbability, strongReuseIdealGame_commonMatrixStrongAttack_apply_true]
    simp [ENNReal.toReal_inv]
  rw [strongReuseAdvantage, Game.coe_advantage, hideal]
  have hsumR : (Game.succProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode)) : ℝ) +
      (Game.failProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode)) : ℝ) =
      1 := by exact_mod_cast hsum
  have hfailR : (Game.failProbability (strongReuseRealGame
      (ProbComp.uniform (Matrix (Fin m) (Fin (k + l)) (ZMod q)))
      (commonMatrixFuzzyExtractor m k l q decode) W t 1 (commonMatrixStrongAttack decode)) : ℝ) ≤
      δ := by exact_mod_cast hfail
  exact le_trans (by linarith) (le_abs_self _)

end CommonMatrix

end Cslib.Crypto.FuzzyExtractor
