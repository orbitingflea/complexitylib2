# Security games and primitive families

## Generic games and adversary quantifiers

[Game](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L67) is a `PMF Bool`. Success is its true probability; advantage is the nonnegative distance between two success probabilities. [Indistinguishable](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Game.lean#L154) says that every admissible complete adversary has negligible advantage as the parameter grows. `Indistinguishable.of_reduction` transfers security through a reduction with a polynomially bounded loss and negligible additive error, while `indistinguishable_pure_false_iff`, `Indistinguishable.of_succProbability_le`, and `Indistinguishable.of_succProbability_reduction` specialize one-sided search and forgery games compared against `PMF.pure false`. This layer is mathematical probability; admissibility determines the computational interpretation [cslib-frontier][complexitylib]. A `PMF` game body can bind the adversary's programs directly with `←` by importing [Lift.lean](../../CslibFrontier/Languages/Probabilistic/Lift.lean) ([Bind a program inside a distribution](../workflows/probabilistic-workflows.md#bind-a-program-inside-a-distribution)).

To write an experiment as the challenger's program, import [Game/Experiment.lean](../../CslibFrontier/Crypto/Game/Experiment.lean). `Experiment` is `ProbComp Bool`, the program whose output distribution is a `Game`. Scheme algorithms, adversaries and experiments are programs, and `ProbComp.eval` appears only in `Experiment.succProbability` and `Experiment.advantage`; as real numbers these are `Pr[e]` and `|Pr[e₀] - Pr[e₁]|` (`Experiment.coe_succProbability`, `Experiment.coe_advantage`). A `…Experiment` is one fixed instance, and a `…Game` is a family: `Game.withSetup setup exp` draws public parameters from a setup law, which need not be efficiently sampleable, and runs the fixed experiment. `Game.advantage_withSetup_le` and `Game.succProbability_withSetup_le` lift a bound that holds at every supported parameter; when the setup is a program such as key generation, `Experiment.advantage_bind_le_of_support` and `Experiment.succProbability_bind_le_of_support` do the same for `setup >>= exp`. `distAdvantage real sim D` is the advantage of a distinguisher between two view distributions, and a perfect simulation gives zero (`distAdvantage_eq_zero_of_eval_eq`). For the bit-guessing form of a pair of experiments, import [Game/HiddenBit.lean](../../CslibFrontier/Crypto/Game/HiddenBit.lean): `Experiment.guessBit e` draws a uniform hidden bit `b`, runs `e b` and wins when the output is `b`; `Experiment.advantage_eq_two_mul_guessingAdvantage_guessBit` says the advantage between `e false` and `e true` is twice its bias, and `Game.uniform_bool_bind_map_beq_const` says a guess drawn independently of the bit is right with probability exactly one half. For adversaries that choose a challenge and then answer, import [Computational/TwoStage.lean](../../CslibFrontier/Crypto/Computational/TwoStage.lean). `TwoStage I₁ O₁ I₂ O σ` keeps a saved state of any type `σ` between its `choose` and `guess` stages. `TwoStage.IsPPT` asks a family indexed by the security parameter for one machine per stage, which reads the unary parameter and the complete encoded stage input, saved state included. The word-level adversaries are the instance `σ := List Bool`. `lrExperiment valid enc A b x` is the challenge phase of single-challenge IND-CPA (Boneh–Shoup Attack Game 11.1) on a drawn public input `x`, with message pairs `MessagePair` encoded by `encMessagePair`; each scheme's experiment draws `x` and calls it, and the simp lemma `eval_lrExperiment` gives its output distribution. The [checked clients](../../CslibFrontierTests/Crypto/Experiment.lean) cover an adversary whose left-or-right advantage is exactly one, a setup bound that depends only on supported parameters, and the derivation of `TwoStage.IsPPT` from a word-level `Encryption.AdversaryOf.IsPPT`. Statements keep named advantages in `ℝ≥0` and write every other probability as `Pr[e]`, with uniform samples as `$ᵗ α` ([State a probability and sample uniformly](../workflows/probabilistic-workflows.md#state-a-probability-and-sample-uniformly)).

For concrete `(t, q, ε)` security bounds, resource-mapping reductions, and bridges to asymptotic security, import [Game/Concrete.lean](../../CslibFrontier/Crypto/Game/Concrete.lean). `Game.IndistinguishableWithin game1 game2 Within ε` bounds `Game.advantage (game1 adversary n) (game2 adversary n) ≤ ε n r` across all adversaries satisfying `Within n r adversary`, and `Game.SuccWithin` (`indistinguishableWithin_pure_false_iff`) is its one-sided success-probability counterpart. `IndistinguishableWithin` supports equivalence/hopping laws (`.refl`, `.symm`, `.trans`, `.mono`, `.of_within`), multi-hop hybrid sums (`.hybrid`, `.hybrid_const`), and concrete reductions (`IndistinguishableWithin.of_reduction`, `SuccWithin.of_reduction`) mapping target resource budgets `r` to source budgets `mapRes n r` with error `loss n r * ε n (mapRes n r) + err n r`. Standard resource predicates `WithinQueries`, `WithinTime`, `WithinTimeUpTo`, `WithinOracleTime`, and `WithinTimeAndQueries` instantiate `Within` over `IsQueryBounded` and the plain halting predicates of [Time.lean](../../CslibFrontier/Computability/Probabilistic/Time.lean) and [Oracle/Time.lean](../../CslibFrontier/Computability/Probabilistic/Oracle/Time.lean); because halting monotonicity needs no computability hypothesis on padded schedules, `indistinguishableWithin_withinTime_iff` and `indistinguishableWithin_withinTimeAndQueries_iff` equate scalar per-parameter bounds with global schedule bounds. To pass from concrete bounds to asymptotic `Game.Indistinguishable`, use `IndistinguishableWithin.indistinguishable` in general, `Game.Indistinguishable.of_queryBounded` / `of_queryBounded_real` / `of_birthday_queryBounded_real` / `of_succProbability_queryBounded` / `of_costBounded` (as in [PseudorandomPermutation.lean](../../CslibFrontier/Crypto/Computational/PseudorandomPermutation.lean) and [LubyRackoff.lean](../../CslibFrontier/Crypto/Computational/LubyRackoff.lean)) for `Q`-query information-theoretic hops, `Game.Indistinguishable.of_queryBounded_reduction` (built on `IsOraclePPT.exists_computable_queryBound`, as in [GGM/Security.lean](../../CslibFrontier/Crypto/Computational/GGM/Security.lean)) when a reduction takes a unary polynomial-time computable query bound `Q`, and `Game.Indistinguishable.of_timeBounded` / `of_timeAndQueryBounded` for computational `(t, ε)` and `(t, q, ε)` bounds. [Checked clients](../../CslibFrontierTests/Crypto/ConcreteSecurity.lean) verify a sharp `q / 2 ^ n` concrete bound with a `1`-query distinguisher achieving exact advantage `2 ^ (-n)`, compose a machine-certified `(t, q) ↦ (2 * t + c + 4, q)` reduction via `IndistinguishableWithin.of_reduction`, and derive asymptotic `IsOraclePPT` security via `of_timeAndQueryBounded`. To write a concrete hop sequence the way the textbooks do, as a `calc` chain of steps `Pr[G₁] ≈[ε] Pr[G₂]`, see [Step game hops](../design-and-assurance/automation.md#step-game-hops-and-align-shared-random-draws).

For reductions whose budgets must preserve many unlike units, import [Game/AttackResources.lean](../../CslibFrontier/Crypto/Game/AttackResources.lean). `AttackResources` derives each static description size from an explicit installed-occurrence inventory: distinct retained copies are charged separately, while a handler, table or compiler hardwired into a retained program is not entered again. Its 13-phase online ledger sums phase times and takes the maximum phase workspace; compiler and final-output accounting refer to those same phases rather than adding duplicate costs. Callers still supply model-specific certificates connecting the ledger, input/output lengths and retained artifacts to an actual execution. `IndistinguishableWithin.indistinguishable_attackResources` only lifts an already proved finite bound along explicit componentwise-polynomial schedules and negligible errors; it neither realizes a machine nor proves a scheme secure. The complete [ordinary module client](../../CslibFrontierTests/Crypto/AttackResources.lean) checks separate, inlined and offline compilation, hardwired versus separate artifacts, exact phase sentinels and the asymptotic bridge.

For native uniform quantum oracle-circuit families, [Game/Quantum.lean](../../CslibFrontier/Crypto/Game/Quantum.lean) specializes the same concrete-to-asymptotic API. `WithinOracleCircuits L n budget family` bounds qubits, elementary gates, coherent queries and the exact `encOracleCircuitDescription` length separately for every classical input length at most `L n`. `Indistinguishable.of_uniformOracleCircuits` derives asymptotic security from a concrete game bound and negligibility along every componentwise polynomial resource schedule; `of_succ_uniformOracleCircuits` handles one-sided success. Native generation supplies the schedules, provided `L` is polynomially bounded. The [checked resource client](../../CslibFrontierTests/QuantumOracleGames.lean) distinguishes equal legacy resources with unequal encodings and gives a conditional transfer with error `(queries² + gates * qubits + descriptionBits) / 2ⁿ`. These are finite-artifact and online-execution budgets: static generator code and offline generator time/workspace are not silently added to adversary runtime. A protocol must still prove the concrete premise and that its game uses only the declared input lengths. These bridges add no quantum-advice quantifier or random-oracle distribution and assert no scheme security theorem.

To quantify native quantum tests directly over word ensembles, import [Computational/Quantum.lean](../../CslibFrontier/Crypto/Computational/Quantum.lean). `NativeQuantum.test family n x` supplies `(1ⁿ, x)` as the classical input, starts every quantum-input qubit at zero, runs against the all-zero XOR oracle, and uses the first terminally measured output bit as the decision; an empty output rejects. `NativeQuantum.distinguishingGame X family n` first draws `x ← X n`, and `NativeQuantum.ComputationallyIndistinguishable X Y` requires negligible advantage for every native `UniformOracleCircuitFamily`. `SupportsLength` and `IndistinguishableWithin` expose the common challenge-length and separate qubit, gate, query and exact-description bounds needed by `ComputationallyIndistinguishable.of_within`. The [checked ensemble client](../../CslibFrontierTests/Crypto/NativeQuantumIndistinguishability.lean) builds one growing family that reads the first challenge bit, proves an exact advantage of one on two point ensembles, and exercises the concrete bridge. This is a zero-advice, no-useful-oracle submodel: it does not supply QROM sampling, quantum advice, gate approximation or an equivalence with every QPPT convention.

For a challenge that first draws a fair bit and then samples the corresponding word ensemble, import [Computational/Quantum/Mixture.lean](../../CslibFrontier/Crypto/Computational/Quantum/Mixture.lean). Write the mixture with the existing `(PMF.uniformOfFintype Bool).bind`; `SupportsLength.bind` propagates a common length cap. `IndistinguishableWithin.bind_uniformBool` averages the two branch bounds as `(ε false n budget + ε true n budget) / 2`, with the same native circuit and the same qubit, gate, query and exact-description budget. `ComputationallyIndistinguishable.bind_uniformBool` gives the asymptotic closure. The [ordinary client](../../CslibFrontierTests/Crypto/NativeQuantumMixture.lean) checks an attained half-advantage, cancellation, zero/one-bit length caps and both fixed-parity HQC assumption interfaces. The mixture is part of challenge sampling; these results do not compile an HQC reduction, charge sampling as a circuit operation, or prove IND-CPA security. Deterministic uniform generators can use the separate `GeneratorCertificate` API; native reduction generators, random coins, executed-generation costs and sampling error remain explicit obligations of [#5281](https://github.com/cslib-community/cslib-frontier/issues/5281).

For finite-source statistical bounds, import [StatisticalDistance/TotalVariation.lean](../../CslibFrontier/Probability/StatisticalDistance/TotalVariation.lean). `Cslib.Probability.closeTo_of_dist_le` turns a bound on the finite-PMF metric (half the L1 distance) into the existing all-event `CloseTo` relation with the same error. The bound is exact on finite types: `closeTo_coe_iff_dist_le` states `CloseTo μ ν ε ↔ dist μ ν ≤ ε` for an error `ε : ℝ≥0`, and `closeTo_iff_ofReal_dist_le` states `CloseTo μ ν ε ↔ ENNReal.ofReal (dist μ ν) ≤ ε` for `ε : ℝ≥0∞`; and `closeTo_iff_etvDist_le` relates `CloseTo` to Mathlib's total variation of `μ.toMeasure` and `ν.toMeasure` on any type with measurable singletons. Its `CloseTo.bind_left` law then handles arbitrary randomized continuations, including infinite output types. The import is pure probability and brings in no games, lattice protocols or native sampler certificates.

For adaptive stateful replacement, import [Security/Oracle.lean](../../CslibFrontier/Computability/Interactive/Security/Oracle.lean). `OracleComp.IsCostBounded.closeTo_runWith` turns a program's existing cost bound `K` and per-call `CloseTo` bounds `cost q * ε` into a bound `K * ε` on the joint result and final state. The premise compares both handlers at every identical query and starting state, including unreachable states; no coupling or finite state space is assumed. Calls of cost zero can still update a shared cache, but their joint reply/state laws must agree statistically at error zero. Charging only signing calls therefore avoids paying for unchanged hash calls or private sampling. The checked adaptive client in [OracleStatistical.lean](../../CslibFrontierTests/OracleStatistical.lean) uses two repeated signing requests, answer-dependent repeated cache reads, and a concrete nonzero error bound while preserving the cache and signing log. This shared lemma does not itself complete the native Schnorr signing-game or key-generation transport in #581. When the two handlers keep different states, related by a probabilistic map (for example a cache and its completed table), use `OracleComp.closeTo_run_interpret_simulation` in [Simulation/CloseTo.lean](../../CslibFrontier/Languages/Probabilistic/Simulation/CloseTo.lean), of which `closeTo_runWith` is the identity case.

For two continuations that agree outside a bad input event, import [Game/CloseTo/UntilBad.lean](../../CslibFrontier/Crypto/Game/CloseTo/UntilBad.lean). `CloseTo.bind_of_eq_on μ f g bad` bounds the mixtures by the actual probability `μ.toOuterMeasure bad`; agreement is required only on supported inputs outside `bad`, and neither type must be finite. This lets a cache-programming step charge only the probability that the sampled point was already cached. The [checked clients](../../CslibFrontierTests/CloseToUntilBad.lean) retain the actual Fiat–Shamir reply and final cache, show a sharp one-half error on an infinite output type, and allow arbitrary disagreement on impossible inputs at zero cost. This law does not identify different hidden cache states or justify removing aborted queries.

For a simulator that retries until an independent coin succeeds, import [Game/Retry.lean](../../CslibFrontier/Crypto/Game/Retry.lean). An attempt returning `Option β` satisfies `ProbComp.eval attempt = μ.bind (tagWith ch)` when its output follows `μ` and its success is an independent coin `ch`; `Game.advantage_bind_firstSuccess_replicate_le` then bounds the advantage of every continuation of `firstSuccess d <$> OracleComp.replicate k attempt` against `μ` by `(ch false) ^ k`. The GMW zero-knowledge simulators use it with `guessCoin`, a uniform 3-bit challenge guess, so `ch false = 7 / 8`. This is a bound on the selected output's law, not a lazy retry loop; for that, use `OracleComp.retry`.

[ComputationallyIndistinguishable](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Basic.lean#L94) specializes admissibility to a uniform native strict-PPT test on `(1^n, sample)`. Its ensembles are arbitrary PMFs on bit strings: sampleability and polynomial output length are not bundled. `IsPPTTest` admits semantic tests whose laws have a native program witness. Efficient postprocessing and hybrid results use those certificates, not the mere presence of a Lean function.

Pinned cslib also has the finite [Generator](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a/Cslib/Crypto/Primitives/PRG/Defs.lean#L38) interface, whose `Secure` accepts any chosen predicate on randomized tests, while expansion is a separate cardinality property. cslib-frontier adds circuit-bounded tests and uniform machine tests on top. These are intentionally different quantifiers; the circuit version can select a new bounded circuit at each input length [cslib][cslib].

### Security theorems and efficiency witnesses

A security theorem says that every admitted adversary has negligible advantage, given a named hardness assumption. [AGENTS.md](../../AGENTS.md#security-theorems) fixes what such a theorem may assume: named hardness assumptions, stated relative to the setup sampler or component they concern; that the adversary is in the admitted class; and properties of components that the cited result itself takes as given. It may assume nothing about an object that its proof constructs, from the adversary or not (a reduction, distinguisher, simulator, extractor or hybrid), and it may not take from the caller an object whose existence or efficiency is what it should prove.

A named assumption may concern the scheme's own components when the cited source assumes it. GSW's one-key circular security `Encryption.CircularSecure E.keyGen E.encrypt`, collision resistance of the Cramer–Shoup hash family `F.withKey.cramerShoupHashMod H` keyed by the hash key that key generation draws and publishes, and quadratic residuosity relative to the scheme's modulus sampler (`QuadraticResiduosityHard fun n => ProbComp.eval (gen n)`) are all allowed. What is ruled out is a premise that the scheme's algorithms behave like idealized ones, such as keys indistinguishable from an ideal key law, unless the cited source names that as an assumption.

Each named assumption belongs in the [assumptions inventory](assumptions.md), which also names the assumptions that its check does not yet find. A *standard* assumption's docstring cites the source definition, with a locator checked at the source, and names every deviation from it, such as an arbitrary setup law where Boneh–Shoup's group parameters come from an efficient algorithm. A *novel* assumption's docstring says that it is novel to this library, how it relates to standard assumptions and why it is plausible. A novel assumption may support an original result whose name mentions it, but not a theorem presented as a cited result. Generic notions such as `Game.Indistinguishable` and `ComputationallyIndistinguishable` are *vocabulary*: they become assumptions through the instance a theorem supplies, and under a cited result review checks that instance against the source. `GMW.AdvicePRG`, for example, is novel and follows from a non-uniform PRG; theorems that rest on it may land only as steps, and the GMW theorem `NonuniformOneWay.exists_zkProof_of_mem_NP` rests on `NonuniformOneWay`. `python3 scripts/check_hardness_assumptions.py` checks the inventory after a build, and `--list` prints the theorems that rest on each assumption.

ElGamal bit encryption under DDH in [ElGamal.lean](../../CslibFrontier/Crypto/Computational/ElGamal.lean) is the reference pattern. It has four parts:

1. **The reduction is a program.** [elGamalMsgToDDHDistinguisher](../../CslibFrontier/Crypto/Computational/ElGamal.lean#L378) turns an IND-CPA adversary into a DDH distinguisher, and `elGamalToDDHDistinguisher` specializes it to bit messages.
2. **A concrete bound.** [advantage_elGamalCPAGame_le](../../CslibFrontier/Crypto/Computational/ElGamal.lean#L661) bounds the IND-CPA advantage of `adversary` by the DDH advantages of `elGamalToDDHDistinguisher adversary false` and `… true`. It holds for every adversary, efficient or not.
3. **An efficiency witness.** [isPPT_elGamalToDDHDistinguisher](../../CslibFrontier/Crypto/Computational/ElGamal.lean#L677) proves that the distinguisher is uniform strict PPT whenever the adversary is.
4. **The asymptotic theorem.** [DDH.elGamalINDCPA](../../CslibFrontier/Crypto/Computational/ElGamal.lean#L684) assumes only `hDDH : F.DDH setup`. For a PPT adversary it applies `hDDH` to both distinguishers through the witness of step 3, and concludes with the bound of step 2.

In the non-uniform circuit model the efficiency witness is a circuit-size bound instead. `secure_truthTableGenerator_booleanFamily` in [GGM/Circuit.lean](../../CslibFrontier/Crypto/Computational/GGM/Circuit.lean) assumes that the generator is secure against tests with `t + 2 ^ n (n C + 1)` gates, a size that the file proves for its reduction.

The statement `F.DDH setup → F.elGamalINDCPA setup` mentions no reduction, so a reader checks it by reading the two definitions `DDH` and `elGamalINDCPA`. A concrete bound such as step 2 is a lemma; on its own it is not a security theorem.

The audit in [#5293](https://github.com/cslib-community/cslib-frontier/issues/5293) (November 2026) found headline theorems on `main` with the premises in the left column. The right column says what the replacement must assume instead.

| Premise found | Why it is ruled out | The replacement assumes |
|---|---|---|
| Schnorr signatures in the random-oracle model: `hDL : Negligible (… oneWayGame … (schnorrFamilyROMSchemeReduction …))` | It is the DL success of the proof's own forking reduction, the hard part of the proof | `F.DiscreteLog setup` and an oracle-PPT forger; the forking reduction gets an `isOraclePPT_…` lemma |
| Goldwasser–Micali: `hkeys`, the public keys of the scheme's own `keyGen gen` are indistinguishable from the ideal key law | It assumes that the scheme's own key generator behaves like an idealized one, which the cited source does not assume | Quadratic residuosity relative to the scheme's modulus sampler, with conditions on that sampler's support; the law of the scheme's keys is proved, not assumed |
| LWE fuzzy extractor: `hlwe`, a bound on the LWE advantage of `hardcoreKeyReduction D` and `hardcoreUniformReduction D` | It bounds constructed reductions instead of assuming LWE | The asymptotic LWE assumption, with certified reductions |
| Fujisaki–Okamoto: `∃ m₀ m₁, m₀ ≠ m₁ ∧ Adv(A) ≤ 2 Adv(romCpaReduction A m₀ m₁) + …` | The messages are chosen after the adversary, so there is no single reduction to certify | A reduction that samples its own messages, against two-stage IND-CPA |
| Σ-protocol knowledge soundness (`SpecialSoundness.efficientKnowledgeSound`): a caller-supplied extractor with its correctness `hE` and its polynomial-time realization `hpoly` as hypotheses | The extractor's existence and efficiency are what a proof of knowledge proves, so supplying it with assumed properties assumes the result | A rewinding extractor built from special soundness, with a PPT certificate |

A lemma may still take a bound on a constructed reduction as a premise when that is the point. [negligible_prediction_of_negligible_inversion](../../CslibFrontier/Crypto/Computational/GoldreichLevin/Parameters.lean#L175) assumes that the inverters built from a predictor have negligible success. Such a lemma is an algebraic helper: its name and docstring say that it is conditional (for example `…_of_reduction_le`), and a theorem that discharges the premise with the reduction's efficiency witness and the named assumption provides the security claim. Here [negligible_parityPrediction](../../CslibFrontier/Crypto/Computational/GoldreichLevin/WordReduction.lean#L194) does so from `OneWay f` through `isPPT_wordInverter`.

Before review, check a new security theorem against this list:

- every premise is a named hardness assumption stated relative to the sampler or component it concerns, the adversary's class membership, or a property of a component that the cited result takes as given;
- each named assumption is in the [assumptions inventory](assumptions.md), cites its source definition or says that it is novel to this library, and, under a cited result, is the source's assumption (or one that it implies) with the source's instance;
- no premise concerns a reduction, distinguisher, simulator, extractor or hybrid that the proof constructs (from the adversary or not), and the caller does not supply an object whose existence or efficiency is what the theorem proves;
- each reduction is a definition with an efficiency witness (`isPPT_…`, `isOraclePPT_…` or a circuit-size bound) that the asymptotic theorem uses;
- the name and docstring state the model (standard, random-oracle, ideal, query-bounded or information-theoretic), the notion (single- or multi-challenge, one-time or many-time, honest-verifier or malicious zero knowledge, semi-honest, static) and any deviation from the cited source;
- a theorem it replaces is deleted or demoted to an honestly named helper in the same change.

CI checks the premise rule on pull requests. After `lake build`, run `python3 scripts/check_security_premises.py` (or `--list CslibFrontier/Crypto/…` for every hit in an area). It reads the elaborated statements of the public Crypto theorems and reports, for each flagged theorem in a changed module, the premise, the kind of claim and the constructed definitions it is about, for example `premise hreduction: negligible about Cslib.Crypto.PrimeOrderGroupFamily.schnorrFamilyROMSchemeReduction`. It also reports a *realization*: a theorem that takes the reduction from the caller as a variable, certifies the variable (`hD : IsOraclePPT encBool D`), and assumes in an equation that it computes the program the proof should build (`hreal : eval (prfRealGame family D n) = … nonceFnDistinguisher … (forger n)`, as in the Carter–Wegman theorems that #5347 deleted). Differences in other modules are printed as a notice, and a change to the checker or its baseline is checked against every module. To fix a report, prove the premise: certify the reduction and apply the named assumption to it. If the lemma is meant to be conditional, name and document it as an algebraic helper (`…_of_reduction_le`, `…_of_isPPTOn`), run `python3 scripts/check_security_premises.py --update-baseline`, and write the one-line `why` of its entry in [security_premises_baseline.json](../../scripts/security_premises_baseline.json). A named assumption about a component the scheme uses, or instantiated at a group or sampler that the library defines, is also flagged; the rule allows it, so its entry says so. When you delete or fix a theorem that has an entry, remove the entry in the same change; the check fails on an entry that no longer matches.

The check supplements review; a clean run is not evidence that a security theorem is right. It does not judge vacuous or misdefined notions, games and assumptions; a wrong or nonstandard assumption, such as an MLWE variant without the short secrets that ML-KEM's security needs; anything outside `Cslib.Crypto`; or names and docstrings that overclaim. Its rules are syntactic, so it also misses a premise whose own definition builds the constructed object, a distribution applied only to numbers or functions (such as a key law at fixed parameters), a bound without an advantage-named constant, a caller-supplied object that the theorem ought to construct, such as the Σ-protocol extractor above, and a realization stated other than as an equation (an inequality, a predicate of the library or a bundled program). Review covers all of these.

CI also checks the witness rule on pull requests. After `lake build`, `python3 scripts/check_reduction_witnesses.py --list CslibFrontier/Crypto/…` lists each reduction of an area with its certificate: a definition that yields a program and that a public theorem uses on the bounding side of an advantage bound, applied to a program variable of the bounded side, such as `B` in `Adv(scheme, A) ≤ Adv(problem, B A)`. A reduction is certified by a theorem that concludes an efficiency certificate mentioning it (`isPPT_elGamalMsgToDDHDistinguisher` for `elGamalMsgToDDHDistinguisher`), as an `abbrev` of certified reductions, or through a certified definition that applies it, such as its word-level program; a query bound is not a certificate. A pull request fails when a changed module has an uncertified reduction that [the baseline](../../scripts/reduction_witnesses_baseline.json) does not record, or a baseline entry that no longer matches. Prove the witness, or, when the bound is information-theoretic or the definition is not a reduction, add an `exempt` entry with its justification. The check does not see a reduction written inline in a bound, a bound without an advantage-named constant, a simulator or extractor on the bounded side, or an attack, and it does not judge whether the witness is the one the asymptotic theorem uses; review covers these.

## Hardness and pseudorandomness

| Schema | Principal source | Formal parameters and main use |
|---|---|---|
| One-way functions | [CslibFrontier/Crypto/Computational/OneWay.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWay.lean) | Deterministic native polynomial evaluation; uniform seed-length sampling; strict-PPT inverter gets unary length and image; any preimage may win |
| Pseudorandom generator | [CslibFrontier/Crypto/Computational/PseudorandomGenerator.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomGenerator.lean) | Length schedule, expansion, native deterministic evaluation and indistinguishability |
| Adaptive pseudorandom function | [CslibFrontier/Crypto/Computational/PseudorandomFunction.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PseudorandomFunction.lean) | Oracle-PPT access, consistent ideal random function, explicit input/output widths and malformed-query convention |
| Collision resistance | [CslibFrontier/Crypto/Computational/CollisionResistant.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CollisionResistant.lean) | Public setup distribution/encoding and input-validity predicate; keyed word specialization; setup need not be efficiently sampleable in the general interface; [DiscreteLog/GroupHash.lean](../../CslibFrontier/Crypto/Computational/DiscreteLog/GroupHash.lean) instantiates it with the Katz–Lindell discrete-logarithm hash (`DiscreteLog.collisionResistantForOn_groupHash`, exact zero-loss reduction for the encoded outputs; fixed digest width, compression and efficient setup are not established), and [RSAHash.lean](../../CslibFrontier/Crypto/Computational/RSAHash.lean) with the Boneh–Shoup RSA hash `H_rsa` (`RSAOneWay.collisionResistantForOn_rsaHash`, when `e` is eventually prime on the key support) |
| Target collision resistance | [CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean](../../CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean), [CslibFrontier/Crypto/Computational/NaorYungUOWHF.lean](../../CslibFrontier/Crypto/Computational/NaorYungUOWHF.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Two-stage pre-key target choice and post-key second-preimage search; polynomial key/block schedules, fixed-depth `2^n`-capacity tree extension, Naor–Yung UOWHFs from `OneWayPermutation`, and Rompel–HHRVW UOWHFs from `OneWay` |
| Inaccessible entropy and shrinking collision grids | [CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), [CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) | Fixed-width native polynomial evaluation, accessible preimage subsets with eventual `1 / denom n` entropy gap, polynomial-size grids of `1`-bit shrinking candidates with an existential random-collision-resistant sequence (`exists_good_candidate`), and uniform `gridCount n`-way cascade concatenation |
| Discrete logarithm and DDH | [CslibFrontier/Crypto/Computational/DiscreteLog.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiscreteLog.lean), [CslibFrontier/Crypto/Computational/DiffieHellman.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/DiffieHellman.lean) | Encoded prime-order group families, exact ideal group laws; public operations and samplers require separate certificates |
| Decisional composite residuosity and Paillier encryption | [CslibFrontier/Crypto/Computational/CompositeResiduosity.lean](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean), [CslibFrontier/Crypto/Computational/Paillier.lean](../../CslibFrontier/Crypto/Computational/Paillier.lean), [CslibFrontier/Crypto/Computational/Paillier/Security.lean](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean), [CslibFrontier/Crypto/Computational/Paillier/Finite.lean](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean) | Factor pairs `(p, q)` of balanced moduli with validity in the type; arbitrary setup law; Paillier encryption with perfect correctness and plaintext-addition preservation under decryption over an abstract strict-PPT modulus generator, which is not constructed; IND-CPA security under DCR with an explicit prime-growth hypothesis; at a fixed modulus, typed Paillier with exactly uniform randomness, full Definition 15.14 and an exact CPA-to-DCR bound |
| Quadratic residuosity, Goldwasser–Micali, RSA, and Rabin factoring | [CslibFrontier/Crypto/Computational/Factoring.lean](../../CslibFrontier/Crypto/Computational/Factoring.lean), [CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [CslibFrontier/Crypto/Computational/GoldwasserMicali.lean](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean), [CslibFrontier/Crypto/Computational/RSATrapdoor.lean](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), [CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean](../../CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean), [CslibFrontier/Crypto/Computational/RSAAttacks.lean](../../CslibFrontier/Crypto/Computational/RSAAttacks.lean), [CslibFrontier/Crypto/Computational/RabinFactoring.lean](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) | Composite Jacobi symbol `jacobiSymbol`, `QR_N` / `QNR_N^{+1}` split and `QuadraticResiduosityHard`; Goldwasser–Micali bit and bounded-word public-key encryption (`KeyDesc`, `blumKeyGen`, `encrypt`, `decrypt`, `mulCiphertexts`, ideal distributional XOR homomorphism, Blum-modulus `INDCPA` from `QuadraticResiduosityHard` and explicit prime growth, ideal-key-law bit and bounded-word bounds, and Jacobi `-1` attack); all-residue and unit-group RSA trapdoor bijection (`rsaEval`, `rsaInvert`, `RSAOneWay`); Blum-integer square roots (`blumSqrt`, `crtSqrt`), `ModulusFactoringHard`, `FactoringHard`, `RabinOneWay`, explicit PPT equivalences `rabinOneWay_iff_factoringHard` and `totientHard_iff_modulusFactoringHard`, and the certified PPT hierarchy `QuadraticResiduosityHard` / `DCR` / `RSAOneWay` / `RSAKeyRecoveryHard` / `TotientHard` $\Rightarrow$ factoring |
| LWE, SIS, and module lattices | [CslibFrontier/Crypto/Computational/LWE/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/LWE/Basic.lean), [CslibFrontier/Crypto/Computational/LWE/Decoding.lean](../../CslibFrontier/Crypto/Computational/LWE/Decoding.lean), [CslibFrontier/Crypto/Computational/LWE/KeyGen.lean](../../CslibFrontier/Crypto/Computational/LWE/KeyGen.lean), [CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean), [CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Basic.lean](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/SIS/Basic.lean), [CslibFrontier/Crypto/Computational/SIS/Ajtai.lean](../../CslibFrontier/Crypto/Computational/SIS/Ajtai.lean), [CslibFrontier/Crypto/Computational/SIS/Module.lean](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), [CslibFrontier/Crypto/Computational/LWE/Module.lean](../../CslibFrontier/Crypto/Computational/LWE/Module.lean), [CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean), [CslibFrontier/Crypto/Computational/LWE/Regev.lean](../../CslibFrontier/Crypto/Computational/LWE/Regev.lean), [CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean](../../CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean), [CslibFrontier/Crypto/Computational/LWE/DualRegev.lean](../../CslibFrontier/Crypto/Computational/LWE/DualRegev.lean), [CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean](../../CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean) | Explicit dimensions, modulus and noise/norm parameters (typed decision-LWE experiments over a finite commutative ring and `2^w` binary matrix words in `LWE/Basic.lean`, shared LWE decoding/key-generation helpers in `LWE/Decoding.lean` and `LWE/KeyGen.lean`, Micciancio–Peikert power-of-two gadget matrices, short kernel matrices (kernel membership, `det S_w = 2^w`, and column norm bounds, without the lattice-basis generation proof), tagged `GenTrap` trapdoors, and deterministic trapdoor LWE inversion in `LWE/Trapdoor/*`, the typed fixed-instance experiment `sisExperiment` over arbitrary nonzero moduli and the family hypothesis `SIS` in `SIS/Basic.lean`, the Ajtai collision-to-SIS bound `ajtaiAdvantage_le_sisAdvantage` in `SIS/Ajtai.lean`, negacyclic `R_q = ℤ_q[X]/(X^n+1)` block-anticirculant expansion `expandModuleMatrix`, `moduleSISExperiment`, `ModuleSIS` and `RingSIS` in `SIS/Module.lean`, typed decision Module-LWE games for any secret and error laws and `DecisionModuleLWE` in `LWE/Module.lean`, Module-LWE public-key encryption in `SIS/ModuleEncryption.lean`, and plain-LWE Regev and GPV dual-Regev bit encryption and IND-CPA security at modulus `2^w` in `LWE/Regev*` and `LWE/DualRegev*`); classical uniform-PPT hardness hypotheses |
| Computational fuzzy extractors | [CslibFrontier/Crypto/Computational/FuzzyExtractor/Basic.lean](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/Basic.lean), [CslibFrontier/Crypto/Computational/FuzzyExtractor/DecodeThenExtract.lean](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/DecodeThenExtract.lean), [CslibFrontier/Crypto/Computational/FuzzyExtractor/DecodeThenExtract/Security.lean](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/DecodeThenExtract/Security.lean), [CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable.lean](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable.lean), [CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable/Encrypt.lean](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable/Encrypt.lean) | Fuller, Meng and Reyzin's `FuzzyExtractor` with correctness and computational security over an explicit source family [fmr20][fmr20]; the sketch-and-extract construction; the LWE construction `FuzzyExtractor.lweFuzzyExtractor` with an advantage bound by two LWE advantages and an asymptotic security step at modulus `2 ^ w`, `FuzzyExtractor.computationallySecure_lweFuzzyExtractor_of_decisionLWEWithErrors`, from decision LWE whose error law is the source, an assumption novel to this library; Apon, Cho, Eldefrawy and Katz's weak and strong reusability experiments (`WeakReuseAdversary`, `StrongReuseAdversary`, `weakReuseAdvantage`, `strongReuseAdvantage`), the common-matrix FMR construction `FuzzyExtractor.commonMatrixFuzzyExtractor` with the reduction step of Theorem 1 (`weakReuseAdvantage_commonMatrixFuzzyExtractor_eq`) and an advantage lower bound for its 1-query strong-reusability attack (`strongReuseAdvantage_commonMatrixStrongAttack_ge`), and the Section 5 encryption-based construction `FuzzyExtractor.lweEncryptFuzzyExtractor` with the reduction step of its security argument (`strongReuseAdvantage_lweEncryptFuzzyExtractor_le`); reduction lemmas only, no reusability security theorem [acek17][acek17] (details below) |

For computational fuzzy extractors, `FuzzyExtractor` formalizes Fuller, Meng and Reyzin's
definitions [fmr20][fmr20] (Definitions 2.1-2.4 of the full version) with `Correct`,
`CorrectWithError` and `ComputationallySecureFor` over an explicit source family and distinguisher
predicate, together with the sketch-and-extract construction of Lemma 2.5. Distinguishers are
`Experiment` programs `Key → Helper → Experiment`, and `FuzzyExtractor.realGame` and
`FuzzyExtractor.idealGame` average the fixed-reading experiments over the source with
`Game.withSetup`.

Construction 4.1 is `FuzzyExtractor.lweFuzzyExtractor` (key = first `k` coordinates of the secret,
no seed). `FuzzyExtractor.securityAdvantage_lweFuzzyExtractor_le` bounds its advantage by two
`LWE.advantage` terms (uniform secret in dimension `l`, error law `W`) of the explicit `Experiment`
reductions `FuzzyExtractor.hardcoreKeyReduction` and `FuzzyExtractor.hardcoreUniformReduction`
(Lemma 4.7 and the security part of Theorem 4.11), and
`FuzzyExtractor.DecoderCorrectWithError.correctHammingWithError_decodeThenExtract` transfers
average-case decoder correctness. `FuzzyExtractor.ComputationallySecure` is the asymptotic form of
`ComputationallySecureFor` for a family indexed by the security parameter.
`FuzzyExtractor.computationallySecure_lweFuzzyExtractor_of_decisionLWEWithErrors` is a step
toward the security part of Theorem 4.11 at power-of-two modulus, not that theorem: Construction
4.1 needs a prime `q`, so apart from modulus `2` it covers no instance of Theorem 4.11, which stays
open at a prime modulus ([#5293](https://github.com/cslib-community/cslib-frontier/issues/5293)).
It proves the family `κ ↦ lweFuzzyExtractor (m κ) (k κ) (l κ) (2 ^ w κ)` secure against uniform
strict PPT distinguishers on every source ensemble for which `DecisionLWEWithErrors l m w source`
holds, given polynomial-time unary parameter schedules. That assumption is decision LWE with the
source as the joint error law, and the [assumptions inventory](assumptions.md) lists it as novel
to this library: it has the form of [fmr20][fmr20] Definition 4.5 as Lemma 4.7 and Theorem 4.11
use it, but at modulus `2 ^ w κ`, outside that definition's range of prime `q`, and against
uniform PPT distinguishers instead of size-bounded ones. `LWEFamily.isPPT_keyReduction` and
`LWEFamily.isPPT_uniformReduction` certify the
reductions. The modulus is `2 ^ w κ`, the modulus of the typed decision LWE.

Not established here: hardness of LWE with error `W` (Theorems 4.6 and 4.8), efficiency of the
honest `Gen`/`Rep`, the Construction 4.9 decoder (Lemma 4.10), and Section 5; the generic
`FuzzyExtractor.decodeThenExtract` carries no security claim. Build with
`lake build CslibFrontier.Crypto.Computational.FuzzyExtractor.DecodeThenExtract.Security`.

For reusable computational fuzzy extractors, [`FuzzyExtractor/Reusable.lean`](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable.lean)
formalizes the experiments of Definitions 2 and 3 of Apon, Cho, Eldefrawy and Katz [acek17][acek17]
in the public-parameters model (`setup : ProbComp PP`,
`fe : PP → FuzzyExtractor (Fin m → ZMod q) Key Helper`). An adaptive `Q`-query adversary
(`FuzzyExtractor.ReuseAdversary`, specialized to `WeakReuseAdversary` with helper-only leakage and
`StrongReuseAdversary` with `(helper, key)` leakage) submits shifts `δ_i : Fin m → ZMod q` clamped
to Hamming weight at most `t` by `FuzzyExtractor.clampShift` (`reuseQueryLoop`). It receives the
real or uniform challenge key only after the queries. `weakReuseAdvantage` and
`strongReuseAdvantage` are `Game.advantage` between the real and ideal experiments averaged with
`Game.withSetup W`. `weakReuseAdvantage_eq_strongReuseAdvantage_toStrong` relates the two
experiments, and `weakReuseAdvantage_zero_eq_securityAdvantage` relates the `0`-query experiment
to `FuzzyExtractor.securityAdvantage`. There is no reusability security predicate: such a
predicate needs a class of efficient adversaries, which is future work. Correctness is averaged
over the public parameters (`FuzzyExtractor.SetupCorrectHammingWithError`) and follows from the
average-case decoder hypothesis `DecoderCorrectWithError` over a uniform matrix. Placing the
matrix `A` in the public parameters gives `FuzzyExtractor.commonMatrixFuzzyExtractor`
(Section 3.3). The reduction step of the proof of Theorem 1 is the exact identity
`FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_eq` against the explicit simulator
`FuzzyExtractor.commonMatrixSimulator`, which gives the concrete bound
`FuzzyExtractor.weakReuseAdvantage_commonMatrixFuzzyExtractor_le` by two LWE advantages of
explicit reductions. If the decoder fails with probability at most `δ` on error `0`, the 1-query
attacker `FuzzyExtractor.commonMatrixStrongAttack` has strong-reusability advantage at least
`1 - δ - 1 / q ^ k` (`strongReuseAdvantage_commonMatrixStrongAttack_ge`).
[`FuzzyExtractor/Reusable/Encrypt.lean`](../../CslibFrontier/Crypto/Computational/FuzzyExtractor/Reusable/Encrypt.lean)
formalizes the standard-model construction of Section 5
(`FuzzyExtractor.lweEncryptFuzzyExtractor`, with helper `EncryptHelper` `(c, B, h)` using
`symEncrypt` and `[3q / 8, 5q / 8]` threshold decryption `symDecrypt`). Decryption is exact when
encryption errors satisfy `8 * (e i).valMinAbs.natAbs + 4 ≤ q`, so the scheme reproduces with
error at most `δ` under `DecoderCorrectWithError decode t δ`
(`DecoderCorrectWithError.setupCorrect_lweEncryptFuzzyExtractor`).
`FuzzyExtractor.strongReuseAdvantage_lweEncryptFuzzyExtractor_le` is the reduction step of the
Section 5 argument: it bounds the `Q`-query strong-reusability advantage of each adversary by two
`(m + (Q + 1) * l)`-row decisional LWE advantages with combined error law
`FuzzyExtractor.encryptLWEErrorLaw W (ProbComp.eval E) Q`, via `encryptRealReduction` and
`encryptIdealReduction`. Not part of these modules: the reusability security theorems themselves
(an adversary class in the reuse experiments, efficiency certificates for the simulator and the
reductions, and the conclusion from `DecisionLWEWithErrors`), and the random-oracle transform of
Section 4 (Theorem 2).

The pseudoentropy gap of
[`Pseudoentropy/Basic.lean`](../../CslibFrontier/Crypto/Computational/Pseudoentropy/Basic.lean)
is `predictionExperiment` on a pair's latent draw `(x, b)`. A typed `SamplablePair.Predictor`
reads `x : pair.Observation n`, and `Predictor.IsPPT` fixes its machine input `(1ⁿ, encode n x)`
with `enc_structure`; open `Cslib.Crypto.Pseudoentropy` and
`Cslib.Crypto.Pseudoentropy.SamplablePair` for the generated rules.
`SamplablePair.hasGapWithAdvice_iff_word` restates the advised gap for word predictors on
`encAdvisedInput` in the word game `Pseudoentropy.predictionGame`, and the word-level extraction
pipeline applies it once, in `HasGapWithAdvice.eventually_indexed_error_ge`.

For the hashed-parity construction, import
[`Pseudoentropy/HashPair.lean`](../../CslibFrontier/Crypto/Computational/Pseudoentropy/HashPair.lean).
`HashPair.Observation` names the public `image`, `index`, `matrix`, `digest` and `query`.
The digest has width `index.val + 1`, while the matrix retains all sampled rows. Its
`encObservation` encoding writes those five fields in that order, with a unary index and every
field except the final query self-delimited. Open `Cslib.Crypto.Pseudoentropy.HashPair` for the
generated field-access certificates; the dependent digest is read as `List.ofFn observation.digest`.
The [checked client](../../CslibFrontierTests/Crypto/HashPair.lean) verifies the exact word layout,
uses the generated certificates to read the image and digest, and exercises zero-width inputs.
`encodeObservation` also accepts a possibly noninjective image map for the sampler's semantic
agreement theorem; the efficient pair uses `encObservation` with an injective image encoding.

For Diffie–Hellman games, import
[`DiffieHellman.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman.lean) and open
`Cslib.Crypto.PrimeOrderGroupFamily`. Fixing `F : PrimeOrderGroupFamily` fixes the family,
its element encodings and its algorithms. A value `d : F.Desc` supplies public group
parameters selecting `F.Carrier d`, `F.order d` and `F.generator d`; `F.encDesc` encodes
those parameters for algorithms. The established names `Desc` and `encDesc` refer to this
parameter type and encoding. For
[`schnorrGroups`](../../CslibFrontier/Crypto/Computational/DiscreteLog/SchnorrGroup.lean),
a parameter bundle contains `(p, q, g)` and proofs of primality and generator validity.
The concrete `d23` in the [DH client](../../CslibFrontierTests/Crypto/DiffieHellman.lean)
uses `(23, 11, 2)`: the subgroup of order `11` modulo `23` generated by `2`.

Each Diffie–Hellman game runs a fixed-group experiment from
[`DiffieHellman/Finite.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean)
in an additive group `G` that is a `ZMod q`-module for some `q ≠ 0` (`[NeZero q]`), with public
element `g`. The CDH and DDH experiments and the DL and CDH self-reductions below also need
decidable equality on `G` (`[DecidableEq G]`). Prime order and generation enter only as hypotheses of
particular bounds. The table sets each step of Boneh–Shoup's
Attack Games 10.5 (CDH) and 10.6 (DDH) [bs23][bs23] beside the corresponding Lean program; `a • g`
is additive notation for the textbook `g^a`.

| Step | Textbook (Boneh–Shoup) | Lean experiment |
|---|---|---|
| CDH challenge | `α, β ←R Z_q`; send `u := g^α`, `v := g^β` | `cdhExperiment q g A`: `a ← $ᵗ ZMod q`, `b ← $ᵗ ZMod q`, `z ← A (a • g) (b • g)` |
| CDH outcome | adversary outputs `ŵ`; it wins if `ŵ = g^(αβ)` | `return z = (a * b) • g`; `cdhAdvantage` is its `Experiment.succProbability` |
| DDH Experiment 0 | `α, β, γ ←R Z_q`; send `(g^α, g^β, g^(αβ))` | `ddhRealExperiment q g D`: `D (a • g) (b • g) ((a * b) • g)` |
| DDH Experiment 1 | `α, β, γ ←R Z_q`; send `(g^α, g^β, g^γ)` | `ddhRandomExperiment q g D`: `D (a • g) (b • g) (c • g)` with an independent `c` |
| DDH outcome | adversary outputs a bit; advantage `abs (Pr[W₀] − Pr[W₁])` | `ddhAdvantage q g D := Experiment.advantage` of the two experiments |

The book's Experiment 0 challenger also draws an unused `γ`; omitting it does not change the
distribution. The experiments draw exact uniform exponents from `ZMod q` and carry no efficiency
certificate.

The family games in `DiffieHellman.lean` draw public group parameters `d` from
`setup n : PMF F.Desc` and run these experiments in `F.Carrier d` with `q = F.order d` and
`g = F.generator d`; each is `Game.withSetup (setup n) fun d => …`:

- `F.cdhGame setup adversary n` runs `cdhExperiment` on `adversary n d`, where
  `adversary : F.CDHAdversary` maps the security parameter, `d` and two elements of `F.Carrier d`
  to a `ProbComp (F.Carrier d)`. `F.CDH setup` says that every adversary with
  `adversary.IsPPT` wins with negligible probability.
- `F.ddhRealGame setup distinguisher n` and `F.ddhRandomGame setup distinguisher n` run
  `ddhRealExperiment` and `ddhRandomExperiment` on `distinguisher n d`, where
  `distinguisher : F.DDHDistinguisher` maps the security parameter, `d` and three elements of
  `F.Carrier d` to a `ProbComp Bool`. `F.DDH setup` says that every distinguisher with
  `distinguisher.IsPPT` has negligible advantage between the two games.

Adversaries receive and return group elements, so a CDH adversary must output a valid element of
`F.Carrier d`. `F.CDH setup`, and with it the conclusion of `DDH.cdh`, is therefore the textbook
CDH assumption, weaker than the word-level assumption against adversaries that may output any word;
[#4783](https://github.com/cslib-community/cslib-frontier/issues/4783) tracks restoring the
word-level form for families with decodable encodings. A DDH distinguisher outputs only a bit, so
`F.DDH setup` is equivalent to the word-level assumption over distinguishers reading the encoded
tuple (`ddh_iff_encoded`), and likewise for `SecureKDF` (`secureKDF_iff_encoded`). To prove such
an equivalence for a new typed adversary, obtain the word adversary with
`IsPPTOn.exists_bool_factor` (or `IsPPTOn.exists_factor`, given an output decoder), passing the
generated layout lemma such as `encDDHInput_apply`. The typed adversary *equals* the word adversary
run on its input's words, so substitute it and apply the word-level assumption, with no
congruence argument for the game. Efficiency is
stated on encodings: `CDHAdversary.IsPPT` and `DDHDistinguisher.IsPPT` ask for one uniform strict
PPT machine that reads `F.encCDHInput` or `F.encDDHInput` and writes the encoded output element or
the output bit. The inputs are the structures `F.CDHInput` (fields `secParam`, `groupParameters`,
`leftPublic`, `rightPublic`) and `F.DDHInput` (adding `candidateShared`); `encCDHInput_apply` and
`encDDHInput_apply` give their layouts: the unary security parameter, the group parameters and the
encoded elements, each framed except the last. Setup remains an arbitrary PMF and acquires no PPT
certificate. Reductions that need exponents use `F.sampleExp n d`, with its `1 / 2 ^ n` statistical
error and separate PPT theorem `isPPTOn_sampleExp`.

`dlToCDHAdversary` and `cdhToDDHDistinguisher` are the elementary reductions behind
`CDH.discreteLog` and `DDH.cdh`. In one group they are `dlToCDH` and `cdhToDDH`, with the bounds
`dlAdvantage_le_cdhAdvantage_dlToCDH` and `cdhAdvantage_le_ddhAdvantage_cdhToDDH_add`. The
random-world half of the latter,
`probability_ddhRandomExperiment_cdhToDDH_le : Pr[ddhRandomExperiment q g (cdhToDDH A)] ≤ 1 / q`,
is the step that the family bound averages over setup. Random self-reducibility ([bs23][bs23],
Exercises 10.8–10.10) works on the same types: `ddhRerandomize` maps a triple `(u, v, w)` to a
uniform real triple when `w` is the Diffie–Hellman element and to a uniform triple otherwise
(`ddhRerandomizeLaw_real`, `ddhRerandomizeLaw_random`); `ddhSelfReduceDistinguisher` is its
efficient form, so `ddh_of_worstCase` derives `F.DDH setup`, with loss `6 / 2 ^ n`, from worst-case
hardness: for every PPT distinguisher there are a real and a non-DDH triple family, which may depend
on the distinguisher, between which its advantage is negligible; and `ddhAmplifiedDecider` turns a
distinguisher with inverse-polynomial fixed-group advantage into one that decides every triple
except with negligible error (`negligible_ddhAmplifiedDecider_error`). For the discrete logarithm
and CDH,
[`DiffieHellman/SelfReduction.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction.lean)
gives the success probabilities of the self-reductions of [bs23][bs23], Theorem 10.2 and
Exercise 10.6, in one fixed group: one attempt of `dlSelfReduce q g A` on `α • g` returns `α` with
probability exactly `ε = dlAdvantage q g A` (`eval_dlSelfReduce_one_smul_some`); if `0 < ε`, then
`n ⌈1 / ε⌉` attempts all fail with probability at most `exp (-n)`
(`eval_dlSelfReduce_smul_none_le_exp`); and on the input `(α • g, β • g)`, `cdhSelfReduce`, which
masks both inputs, returns `(α * β) • g` with probability equal to the CDH advantage
(`eval_cdhSelfReduce_smul_apply`).
[`DiffieHellman/SelfReduction/Family.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/SelfReduction/Family.lean)
states them over a `PrimeOrderGroupFamily`, for word-level adversaries and with masks drawn by
`sampleExp`. If the adversary is uniform strict PPT, so are the masked call
(`isPPTOn_dlSelfReduceAdversary`) and the CDH reduction (`isPPT_cdhSelfReduceAdversary`), and so is
the checked loop when its number of attempts `k n` is computable in polynomial time in unary
(`isPPTOn_dlSelfReduceRetryAdversary`). On the encoding of `α • g`, one checked attempt returns
a nonempty word that reads as `α` with probability at least `ε - 1 / 2 ^ n`, where `ε` is the
adversary's success in that group (`le_toOuterMeasure_dlSelfReduceRetryAdversary_one`); the
inequality is the sampling loss. The bound is stated on the output word because the empty word,
which stands for `fail`, reads as the exponent `0`: the bound on the exponent that the game reads
(`le_eval_discreteLogAdversary_dlSelfReduceRetryAdversary_one`) holds for every loop at `α = 0`.
Let `invEps` be computable in polynomial time in unary, and suppose that for all large `n`,
`0 < invEps n` and the adversary wins in the group `d n` with probability at least
`1 / invEps n`. Then on the encodings of every sequence of instances `α n • g` in `d n`, the loop
with `n * (2 * invEps n)` attempts errs, returning the empty word or a word that does not read as
`α n`, with negligible probability (`negligible_dlSelfReduceRetryAdversary_error`).
For every setup law, the masked call's success against fixed instances `α d • g` is within
`1 / 2 ^ n` of the adversary's average-case success
(`advantage_dlWorstCaseGame_discreteLogGame_le`), and the CDH reduction's against fixed pairs
`(α d • g, β d • g)` within `2 / 2 ^ n` (`advantage_cdhWorstCaseGame_cdhGame_le`). So
`discreteLog_of_worstCase` and `cdh_of_worstCase` derive `F.DiscreteLog setup` and `F.CDH setup`
when every uniform strict PPT adversary has instances, which may depend on it, against which it
wins with negligible probability. The
[self-reduction client](../../CslibFrontierTests/Crypto/DiffieHellmanSelfReduction.lean) shows
where `0 < ε`, injectivity of `c ↦ c • g` and masking both CDH inputs are needed; the
[family client](../../CslibFrontierTests/Crypto/DiffieHellmanSelfReductionFamily.lean) applies the
family results to the adversary that always guesses `0`.
Fixed-first-coordinate rerandomization, single-exponent shifting, and Multi-DDH (I) ([bs23][bs23],
Exercises 10.8, 10.9, and 10.11) live in
[`DiffieHellman/MultiDDH.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/MultiDDH.lean),
providing both the finite-index and block distributional laws (`ddhFixedURerandomizeLaw`,
`multiDDHRerandomizeLaw`, `ddhShiftAndRerandomizeLaw`) and the `ProbComp` reductions and uniform
strict PPT witnesses (`ddhFixedUSelfReduceDistinguisher`,
`singleSecretMultiDDHToDDHDistinguisher`, `DDH.singleSecretMultiDDH`,
`multiDDHToDDHDistinguisher`, `DDH.multiDDH`). The
[DH client](../../CslibFrontierTests/Crypto/DiffieHellman.lean) checks the DDH input layout,
runs the CDH-to-DDH reduction and the rerandomization on concrete `d23` elements, and
instantiates the amplified decider; the
[Multi-DDH client](../../CslibFrontierTests/Crypto/MultiDDH.lean) checks fixed-first-coordinate
rerandomization, single-exponent shifting, and both `DDH.singleSecretMultiDDH` and
`DDH.multiDDH` on concrete PPT distinguishers. The
[nonvacuity client](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) evaluates the real
and random games with fixed group parameters to probabilities `1 / q` and `1 / q²` for the same
efficient identity test, and shows that constant composite, Blum, and RSA moduli fail
`ModulusFactoringHard`, `FactoringHard`, `RabinOneWay`, `QuadraticResiduosityHard`, `DCR`,
`TotientHard`, `RSAKeyRecoveryHard`, and `RSAOneWay` against a constant-factor adversary
`constFactors`. From the repository root, check these clients with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.DiffieHellman CslibFrontierTests.Crypto.MultiDDH CslibFrontierTests.Crypto.AssumptionNonvacuity
```

In a group of even order, the parity test of [bs23][bs23], Section 16.1.3, distinguishes
Diffie–Hellman triples from random ones. Import
[`DiffieHellman/EvenOrder.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean).
For `G` a `ZMod q`-module with `q` nonzero and even (`[NeZero q]`, `Even q`) and `c ↦ c • g`
injective, `div_two_nsmul_smul_eq_zero_iff` (Lemma 16.1) and `even_val_mul_iff` (Lemma 16.2) read
the parity of `a.val` and `(a * b).val` from `(q / 2) • _`, and, with `[DecidableEq G]`,
`ddhAdvantage_ddhParityDistinguisher` proves that the parity test `ddhParityDistinguisher q` has
fixed-group advantage exactly `1 / 2`. `ddhAdvantage_units_ddhParityDistinguisher` instantiates
this for `(ZMod p)ˣ` with `p` an odd prime (`[Fact p.Prime]`, `p ≠ 2`) and any generator `g`
(`hg : ∀ x, x ∈ Subgroup.zpowers g`), under the local instances `zmodUnitsModule p` and
`neZero_sub_one_of_prime p`. The fixed-group advantage does not bound the distinguisher.
Efficiency is stated over group families whose order need not be prime:
[`DiscreteLog/CyclicGroupFamily.lean`](../../CslibFrontier/Crypto/Computational/DiscreteLog/CyclicGroupFamily.lean)
defines `CyclicGroupFamily` (a `PrimeOrderGroupFamily` with `order_ne_zero` and
`smul_generator_injective` in place of `prime_order` and `generator_ne_zero`) and
`PrimeOrderGroupFamily.toCyclicGroupFamily`, and
[`DiffieHellman/CyclicGroupFamily.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/CyclicGroupFamily.lean)
states its DDH assumption `CyclicGroupFamily.DDH`, which on a prime-order family is
`PrimeOrderGroupFamily.DDH` (`ddh_toCyclicGroupFamily_iff`). There the certificate
`CyclicGroupFamily.isPPT_ddhParityDistinguisher` shows that the parity test is computed by one
uniform strict PPT machine on `encDDHInput`, so Exercise 10.24's distinguisher is efficient, and
`CyclicGroupFamily.not_ddh_of_even_order` proves that DDH does not hold when every group the setup
law can produce has even order. No family of the groups `(ZMod p)ˣ` is constructed, so the book's
conclusion that DDH does not hold in `Z_p^*` is proved only in the fixed-group form. The
[even-order client](../../CslibFrontierTests/Crypto/DiffieHellmanEvenOrder.lean) checks `ZMod 6`,
`(ZMod 7)ˣ` and the odd-order failure of Lemma 16.1 in `ZMod 5`, applies
`not_ddh_of_even_order` to the residue groups `ZMod (2 (n + 1))`, and derives that a prime-order
family fails `PrimeOrderGroupFamily.DDH` for any setup law that only produces groups of order `2`.

Inversion and prediction are each stated once, for a fixed function and input distribution, in
[`Crypto/Game/Inversion.lean`](../../CslibFrontier/Crypto/Game/Inversion.lean):
`inversionExperiment sample f A` draws `x`, gives `A` the image `f x` and accepts any preimage,
and `predictionExperiment sample f h P` asks `P` for the bit `h x` given `f x`. The word games
`inversionGame` (one-wayness) and `predictionGame` (hard-core predicates) run them on uniform
`n`-bit inputs, and the finite Goldreich–Levin reduction uses the same inversion experiment on
`PMF.uniformOfFintype (BitString n)`; `ProbComp.eval_inversionExperiment` moves a program
experiment to its distribution. Instantiate these experiments for a new inversion-style notion
instead of writing another sampling block. The inner product of bit lists is
[`BitString.listDot`](../../CslibFrontier/Foundations/Data/BitString/List/Dot.lean), which is
Mathlib's `dotProduct` on `List.ofFn` inputs (`listDot_ofFn`); use it, and its polynomial-time rule
`ComputableInPolyTime.bitsListDot`, instead of spelling out the zip-and-fold parity.

For a one-bit expanding PRG, [Stretch/Prefix.lean](../../CslibFrontier/Crypto/Computational/Stretch/Prefix.lean)
proves that `(forwardIterate g ℓ seed).take ℓ` has length `ℓ` and agrees with the first `ℓ`
emitted bits of every longer run. The premise is global: `length (g seed) = length seed + 1`
for every seed, including the empty word. The complete `forwardIterate` output also retains a
reversed final seed and is not prefix-consistent. Native computation charges both the seed and
unary `ℓ`; for each uniform native length schedule `L n`, the emitted `L n`-bit prefix from a
uniform `n`-bit seed is computationally indistinguishable from `uniformList (L n)`, by existing
stretch security and reverse/take postprocessing. [PRGStretch clients](../../CslibFrontierTests/PRGStretch.lean)
check zero widths, order-sensitive output, and native XOR encryption/recovery. This is the emitted-pad
prerequisite for the stream-cipher route of Boneh–Shoup §3.2 [bs23][bs23]; adaptive arbitrary-word
one-time encryption and hash-then-MAC/EtM remain open in [#2749](https://github.com/cslib-community/cslib-frontier/issues/2749).

The Ideal Cipher Model models a block cipher as a key-indexed family of independent random permutation oracles supporting forward and inverse queries. [`IdealCipher.lean`](../../CslibFrontier/Languages/Probabilistic/IdealCipher.lean) formalizes lazy exact and forgetful ideal-cipher caches, proves partial bijection preservation (`uniform_interpret_eq_lazy`), and bounds the distinguishing advantage between a uniform ideal cipher and the forgetful sampler by `(Q.choose 2) * |Block|⁻¹` (`abs_sub_uniformPerm_forgetful_le`). Built upon this, [`Compression.lean`](../../CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean) models collision resistance (`collisionGame`), records the probability-`1` inverse-query attack on `cipherOutput` (`cipherOutputAdversary_wins`, [katzlindell20][katzlindell20] Exercise 7.23(a)), and proves the Davies–Meyer Ideal-Cipher collision-resistance upper bound of `2 * ((Q + 2).choose 2) * |Block|⁻¹ = ((Q + 2) * (Q + 1)) * |Block|⁻¹` for every `Q`-query adaptive adversary (`daviesMeyer_collisionGame_le`, `daviesMeyer_collisionGame_mul_le`; [katzlindell20][katzlindell20] Theorem 7.5), checked nonvacuously in [`CslibFrontierTests/Crypto/IdealCipherCompression.lean`](../../CslibFrontierTests/Crypto/IdealCipherCompression.lean).

For the generic group model of Boneh–Shoup ([bs23][bs23], §16.3), import
[`GenericGroup/Basic.lean`](../../CslibFrontier/Crypto/Computational/GenericGroup/Basic.lean).
`answer L` is the group oracle of a labeling `L : ZMod q → S`: it answers labeling queries
and group operations `(ℓ₁, ℓ₂, κ₁, κ₂)`, and rejects with `none` when `ℓ₁` or `ℓ₂` is not a
label. `groupAnswer q g` is the oracle of a `ZMod q`-module with base point `g`; it is `answer`
for the labeling `β ↦ β • g` when every element is a multiple of `g` (`groupAnswer_eq_answer`).
[`GenericGroup/BabyStepGiantStep.lean`](../../CslibFrontier/Crypto/Computational/GenericGroup/BabyStepGiantStep.lean)
states the baby-step/giant-step algorithm of §16.1.1 as a program over this oracle, with `m`
baby and `n` giant labels, and proves that, for `q ≠ 0`, it outputs the discrete logarithm when
`q ≤ m * n` and the labeling is injective (`evalPure_babyStepGiantStep`,
`evalPure_groupAnswer_babyStepGiantStep`). Its efficiency certificate in the generic group
model is a query bound on the program: every call is a product of two labels
(`queriesSatisfy_babyStepGiantStep`), and every run makes at most `(m - 1) + (n - 1)` calls
(`isQueryBounded_babyStepGiantStep`), which is `2 * Nat.sqrt (q - 1)` at the book's table size
(`babyStepGiantStep_sqrt`). The giant steps multiply by the label of `m` instead of the book's
`g^(-m)`; the module documentation lists this and the other differences from the book. No running
time in a machine model is stated. Runs and instances showing that each hypothesis is needed are in
[`GenericGroup.lean`](../../CslibFrontierTests/Crypto/GenericGroup.lean) and
[`GenericGroupRuns.lean`](../../CslibFrontierTests/Crypto/GenericGroupRuns.lean).

The lower bound for discrete logarithm in this model, Theorem 16.3 ([bs23][bs23], §16.3,
pp. 693–695), is in
[`GenericGroup/DiscreteLog.lean`](../../CslibFrontier/Crypto/Computational/GenericGroup/DiscreteLog.lean).
`dlogGame A` draws a uniform injective labeling `L : ZMod q ↪ S` and a uniform `α`, gives the
adversary `L 1` and `L α`, runs it against `answer L` (`runLabeled`), and is won when the
adversary outputs `α`. For a prime `q` (`hq : q.Prime`, with the instance `NeZero q`), a finite `S`
with `Nonempty (ZMod q ↪ S)` (the book's `|S| ≥ q`) and an adversary `A` with
`(A g u).IsQueryBounded T` for all `g u` (at most `T` labeling and group-operation queries on every
path; private coins are free), `succProbability_dlogGame_le` bounds the success probability by
`((3T + 2)² / 2 + 1) / q`, the book's (16.6), and `succProbability_dlogGame_le_choose` by the
sharper `((3T + 2).choose 2 + 1) / q`. The bound takes no hardness assumption and applies to
adversaries that are otherwise unbounded, but it is about the model only: it says nothing about
discrete logarithm in any specific group (p. 695). As in the book, `q` is prime; the bound is not
claimed for composite `q`. The proof reduces labels in `S` to a uniform permutation of `ZMod q` with
[`GenericGroup/Relabel.lean`](../../CslibFrontier/Crypto/Computational/GenericGroup/Relabel.lean):
`relabel j A` answers each query of `A` with at most one query (`isQueryBounded_relabel`) and
behaves against a permutation `σ` as `A` against `j ∘ σ` (`runLabeled_relabel`). Checked
examples, including where the proof uses primality, are in
[`GenericGroupDiscreteLog.lean`](../../CslibFrontierTests/Crypto/GenericGroupDiscreteLog.lean).

For a fixed keyed function or block cipher over finite types, import [`Primitives/PRF/Finite.lean`](../../CslibFrontier/Crypto/Primitives/PRF/Finite.lean) and [`Primitives/PRP/Finite.lean`](../../CslibFrontier/Crypto/Primitives/PRP/Finite.lean) (Boneh–Shoup §4.1–§4.4 [bs23][bs23]). A `PRF.Adversary D R` is an adaptive oracle program with private coins. `PRF.realExperiment F A` and `PRF.idealExperiment A` are `ProbComp Bool` programs answering its queries with `F key` for a uniform key or with a uniform function `D → R`, and `PRF.advantage` is the distance between their laws. For a block cipher `E : Key → Equiv.Perm D`, `PRP.realExperiment E` is the PRF experiment of `E` and `PRP.idealExperiment` samples a uniform permutation. The switching lemma `PRP.advantage_idealExperiment_prfIdealExperiment_le` bounds the distance between the two ideal experiments by `Q.choose 2 / |D|` for a `Q`-query adversary (Theorem 4.4), and `PRP.prfAdvantage_le_advantage_add` is Corollary 4.5. `PRP.strongRealExperiment` and `PRP.strongIdealExperiment` also answer inverse queries through `RandomPermutation.PermOracleSpec D`; `PRP.StrongAdversary.ofForward` runs a forward adversary there with the same advantage (`PRP.strongAdvantage_ofForward`). These statements are single-instance and track no running time. The word-level `BlockCipher.PRP` switching lemma `advantage_prpIdealGame_prfIdealGame_le` is derived from the finite one. [`Computational/PseudorandomFunction/Finite.lean`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/Finite.lean) connects the two levels: `PRF.atLevel family n` is a word family read as a keyed function on `n`-bit strings, and `PRF.advantage_atLevel_adapt` shows that, for a length-preserving family, the finite advantage against it of a word distinguisher `A` read through `OracleCodec.bitString n` is the advantage of `A` between `prfRealGame id family A n` and `prfIdealGame id id A n`. A finite argument therefore transfers to `PseudorandomFunction` once its adversary is exhibited as an adapted oracle-PPT word program. Checked examples of the finite experiments and the switching lemma are in [`CslibFrontierTests/Crypto/PseudorandomPermutation.lean`](../../CslibFrontierTests/Crypto/PseudorandomPermutation.lean); the bridge, `PRF.label` and `labelCodec` are checked on concrete families and tables in [`CslibFrontierTests/Crypto/PRFLabel.lean`](../../CslibFrontierTests/Crypto/PRFLabel.lean).

Several independently keyed copies of a pseudorandom function are again pseudorandom: [`PseudorandomFunction.multiKey`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/MultiKey.lean) answers `t` word channels with the `n`-bit blocks of one `t * n`-bit key, against `t` independent random functions, for every fixed `t`. Its hybrid reduction `prfMultiReduction` simulates the already random channels with a lazy list cache and is itself oracle PPT; the concrete bound sums `t` PRF advantages (Boneh–Shoup, Exercise 4.26). The number of keys is a constant, not a function of the security parameter; the exercise also allows a polynomially bounded number of keys, which this theorem does not cover. The finite counterpart is [`Primitives/PRF/MultiKey.lean`](../../CslibFrontier/Crypto/Primitives/PRF/MultiKey.lean): for a keyed function `F : Key → D → R` on finite types and an adversary with private coins and `t` channels, `PRF.multiKeyAdvantage_le_sum` bounds the distance between `t` independent uniform keys and `t` independent uniform functions by `∑ j < t, PRF.advantage F (PRF.multiKeyReduction F j A)`. Each reduction is one randomized `PRF.Adversary D R` that samples its own keys, forwards channel `j`, and lazily samples the channels below `j` with a list cache; it makes at most as many queries as `A` (`PRF.isQueryBounded_multiKeyReduction`).

For keyed functions that call a random oracle, import [`Primitives/PRF/RandomOracleModel.lean`](../../CslibFrontier/Crypto/Primitives/PRF/RandomOracleModel.lean) ([bs23][bs23], §8.10.2, Attack Game 8.4 and Theorem 8.9, p. 329). A `PRF.ROAdversary X Y M T` is one adaptive program with private coins that asks for the keyed function at `x : X` with the query `Sum.inl x`, answered in `Y`, and for the random oracle at `m : M` with the query `Sum.inr m`, answered in `T`. For finite types `Key`, `X`, `Y`, `M` and `T`, with decidable equality on `X` and `M` and with `Key`, `Y` and `T` nonempty, `PRF.roRealExperiment F A` samples the whole oracle table `O : M → T` and one uniform key and answers the keyed queries with `F O key`, for `F : (M → T) → Key → X → Y`; `PRF.roIdealExperiment A` samples the whole table and one uniform function `X → Y`; both answer the oracle queries with `O`, and `PRF.roAdvantage F A` is their distinguishing advantage. `A.IsOracleQueryBounded Q` says that `A` makes at most `Q` random-oracle queries on every path, whatever its coins and the replies; it counts neither the queries `Sum.inl x` nor private samples. `PRF.roAdvantage_prependKey_le` proves Theorem 8.9: for finite types `Key`, `X`, `M` and `T`, with decidable equality on `X` and `M` and with `Key` and `T` nonempty, for `encode : Key → X → M` with `Function.Injective2 encode`, and for `A : PRF.ROAdversary X T M T` with `A.IsOracleQueryBounded Q`, the advantage `PRF.roAdvantage (PRF.prependKey encode) A` of the key-prepending function `PRF.prependKey encode O key x = O (encode key x)` is at most `Q / Fintype.card Key`, whatever the adversary's other queries, coins and running time. Both halves of injectivity are needed: [`RandomOraclePRF.lean`](../../CslibFrontierTests/Crypto/RandomOraclePRF.lean) checks a pairing that is constant in the input, against which an adversary without random-oracle queries has advantage `1 / 2` where the bound would be `0`, and a pairing that sends every key to the same point, against which one random-oracle query gives advantage `1 / 2` for every number of keys. `PRF.keyAppend κ L` gives the book's `k ‖ x`, a `κ`-bit key followed by a word of `shortWords L`, and `PRF.roAdvantage_prependKey_keyAppend_le` bounds the advantage of an adversary with `A.IsOracleQueryBounded Q` against it by `Q / 2 ^ κ` for every finite nonempty `T`. Over a security parameter `n`, with `Key n`, `X n`, `M n` and `T n` finite, decidable equality on `X n` and `M n`, and `Key n` and `T n` nonempty for every `n`, `PRF.negligible_roAdvantage_prependKey` makes the advantage negligible for every family of adversaries whose numbers of random-oracle queries are bounded by a polynomially bounded `Q`, provided that `encode n` is injective in the pair for every `n` and that `1 / Fintype.card (Key n)` is negligible; for finite nonempty `T n` at every `n`, `PRF.negligible_roAdvantage_prependKey_keyAppend` gives the same for `keyAppend (κ n) (L n)` when `n ≤ κ n` for every `n`. Neither statement asks the adversaries to be efficient. Nothing is claimed about `H(k ‖ x)` for a concrete hash function `H` (for a Merkle–Damgård hash the book shows it insecure, §8.7), Definition 8.5 is not a named predicate, and no lower bound on the advantage is proved.

Unconditionally, any pseudorandom function on `n`-bit inputs requires at least `2 * n - 2` binary gates over the full binary Boolean basis `B₂` (`fullInterpretation (k := 2)`) on all but a negligible fraction of keys (Fan–Li–Yang §§4.2, 7.1, Theorem 7.5 [fly22][fly22]): [`CircuitLowerBound.lean`](../../CslibFrontier/Crypto/Computational/PseudorandomFunction/CircuitLowerBound.lean) proves the bound both for arbitrary `BooleanPRF` ensembles (which impose no efficient sampling or evaluation condition) and for word-valued `PseudorandomFunction` families via deterministic `BitString.lowBits`-encoded restriction queries. The underlying wire out-degree, syntactic dead-gate elimination (`Circuit.NoDeadGates`), critical-path `2 * n - 2 * m` gate bound, and `B₂` intersection bottleneck live in [`CslibFrontier/Computability/Circuit/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/CriticalPath.lean) and [`CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean`](../../CslibFrontier/Computability/Circuit/Boolean/CriticalPath.lean). Tightness at `2 * n - 2`, distinguisher completeness, refutation of bitwise XOR, unconditional `BooleanPRF` non-vacuity on random functions, and conditional `OneWay` non-vacuity are checked in [`CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean`](../../CslibFrontierTests/Crypto/PRFCircuitLowerBound.lean).

The main uniform construction chain is [OneWay.exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRG.lean#L54), [exists_oneWay_iff_exists_pseudorandomGenerator](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/PRGToOneWay.lean#L215), polynomial stretch, and [OneWay.exists_pseudorandomFunction](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToPRF.lean#L46). The formal abstract [hill](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/abstracts/ComplexityAbstracts/CryptographyAbstract.lean#L81) (since retired) stated the one-bit expansion endpoint, and `adaptive_functions` stated the adaptive PRF endpoint, as restatements of `OneWay.exists_pseudorandomGenerator` and `OneWay.exists_pseudorandomFunction`. The forward generator proof follows the Holenstein pseudoentropy route to the Håstad–Impagliazzo–Levin–Luby theorem; the function construction follows Goldreich–Goldwasser–Micali. The cited primary sources establish the classical OWF/PRG and adaptive function-construction results [hill99][hill99] [holenstein06][holenstein06] [ggm86][ggm86]. The uniform Lean endpoint does not assume an extra entropy or nonuniform-advice premise. In parallel, relativizing the Holenstein pseudoentropy, three-source, entropy-grid, XOR-combination and reindexing pipeline to polynomially bounded advice families yields the nonuniform construction chain [`NonuniformOneWay.exists_nonuniformPRG`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L68) (one-bit stretch) and [`NonuniformOneWay.exists_nonuniformPRG_three_mul`](../../CslibFrontier/Crypto/Computational/OneWayToPRG.lean#L77) (length-tripling `3 * n + 1` stretch) from any [`NonuniformOneWay`](../../CslibFrontier/Crypto/Computational/Nonuniform/Basic.lean#L290) function.

Target collision resistance (universal one-wayness) separates target selection from key sampling: in [`TargetCollisionResistant.lean`](../../CslibFrontier/Crypto/Computational/TargetCollisionResistant.lean), `TargetCollisionFinder.choose` commits to `(m₀, state)` from `1^n` before a uniform `keyLen n`-bit key is drawn, and `TargetCollisionFinder.find` receives `(1^n, state, k)` to output `m₁` (Boneh–Shoup §8.11.2, Attack Game 8.5 and Definition 8.7 [bs23][bs23]; Naor–Yung §2 [naoryung89][naoryung89]; Goldreich §6.4.3 [goldreich04][goldreich04]). Full collision resistance implies target collision resistance with identical game success probability (`CollisionResistantOn.targetCollisionResistantOn`). Because single-key Merkle–Damgård requires the key to compute intermediate chaining targets, domain extension from `KeyedCompressionFamily` (`2M(n) → M(n)` with `n ≤ M(n)`) to unrestricted `KeyedHashFamily` on `List Bool` instead uses `uowhfTreeHash`, a total fixed-depth adaptation of level-keyed binary-tree hashing (Naor–Yung 1995 revision §2.3 [naoryung89][naoryung89]; Goldreich June 2003 chapter draft §6.4.3.2, Constructions 6.4.24/6.4.26 and Propositions 6.4.25/6.4.27 [goldreich04][goldreich04]; cf. Boneh–Shoup §8.11.3, pp. 339–340 [bs23][bs23], which instead presents a chain that reuses one compression key with `1 + log₂ L` XOR masks, so that its key is logarithmic in the message length, and mentions a tree-based alternative): `uowhfLeaves` encodes one message bit per zero-padded `M(n)`-bit leaf, `uowhfTreeLevels` folds `n` fixed halving levels under independent subkeys, `top.headD []` selects the first resulting block, and an `(n + 1)`-st subkey compresses that block with `BitString.lowBits (M n) msg.length` (`msg.length mod 2^{M(n)}`). At fixed `n`, inputs longer than `2^n` bits leave multiple blocks in `top` and `top.headD []` discards the extra roots (so out-of-capacity messages such as `[false, false, false]` and `[false, false, true]` at `n = 1` collide), whereas `KeyedCompressionFamily.targetCollisionResistant_treeHash` still holds on unrestricted `List Bool` because strict-PPT admissibility polynomially bounds the output lengths of both `choose` and `find`, placing supported `m₀` and `m₁` strictly below `2^n ≤ 2^{M(n)}` for all sufficiently large `n`; [`CslibFrontierTests/Crypto/TargetCollisionResistant.lean`](../../CslibFrontierTests/Crypto/TargetCollisionResistant.lean) gives checked instances, collision extractions and insecurity witnesses. In [`NaorYungUOWHF.lean`](../../CslibFrontier/Crypto/Computational/NaorYungUOWHF.lean), any `OneWayPermutation` instantiates that compression interface without trapdoors (adapting Naor–Yung §3 [naoryung89][naoryung89] and Goldreich June 2003 draft §6.4.3.2, Construction 6.4.20 and Proposition 6.4.21 [goldreich04][goldreich04]): `naorYungShrink` quotients `{0, 1}^{n+2}` by `{0, δ}` via pivot-bit canonicalization and deletion rather than an affine/Toeplitz matrix so `naorYungStep` reduces to `inversionGame` at length `n + 2` with exact loss `1` and zero additive error, `naorYungCompression` cascades `n + 1` steps (`2(n + 1) → n + 1`) with loss `dyadicSize (n + 1)`, and `naorYungHash` composes with `KeyedCompressionFamily.treeHash` (`OneWayPermutation.targetCollisionResistant_naorYungHash`, `OneWayPermutation.exists_targetCollisionResistant_keyedHashFamily`; client checks and an explicit `1 / 2`-success break of `naorYungStep id` are in [`CslibFrontierTests/Crypto/NaorYungUOWHF.lean`](../../CslibFrontierTests/Crypto/NaorYungUOWHF.lean)).

For universal one-way hashing from general one-way functions without permutations, [`OneWay.rompelBase_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean), [`OneWay.exists_rompelBase_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean), and [`OneWay.exists_inaccessibleEntropyFamily_logGap`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/OneWay.lean) prove Haitner–Holenstein–Reingold–Vadhan–Wee, Section 4.2, Theorem 4.5 [hhrvw20][hhrvw20] from any uniform `OneWay` function via the `3`-wise independent Boolean affine hash family [`isThreeWiseIndependentHash_affineHash`](../../CslibFrontier/Probability/BitString/AffineHash/ThreeWise.lean), prefix-collision seed projection `adjustAffineSeed`, and dyadic `(Nat.log 2 n + 1)`-bit saturating prefix field: one single uniform polynomial-time base family `rompelBaseEvalWord g outLen` achieves an eventual `d * Real.logb 2 n / n` gap between real Shannon conditional entropy and accessible average max-entropy for every constant `d > 0` against uniform strict-PPT adversaries, witnessed at each `d > 0` by the adversary-independent accessible-set family `rompelAccessibleSet c g outLen` with polynomial light-image threshold `4 * (n + 1) ^ c * |g⁻¹(y)| ≤ 2 ^ (n - min r n)` (`rompelLightImages c`) and packaged as an [`InaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean) with integer gap denominator `rompelGapDenom c n = 64 * (n + 1) / (c * Nat.log 2 n + 1) + 1 = Θ(n / log n)` (`OneWay.exists_inaccessibleEntropyFamily` instantiates `d = 1`). [`AdversaryInaccessibleEntropyFamily`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Basic.lean) states [hhrvw20][hhrvw20] Section 3.2, Definition 3.9 (p. 15) directly with adversary-dependent accessible preimage sets (`∀` uniform strict-PPT `IsWordCollisionFinder`, `∃ accSet` satisfying `IsAccessibleEntropyWitness`); word-level fallback sanitization `sanitizeWordCollisionFinder` lifts Definition 3.9 to arbitrary uniform strict-PPT adversaries (`AdversaryInaccessibleEntropyFamily.exists_accessibleSet`), and `InaccessibleEntropyFamily.toAdversaryInaccessibleEntropyFamily` embeds any fixed-witness family into it. Parallel repetition with Hoeffding concentration and dyadic planted-coordinate escape reductions ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Repetition.lean), Lemma 5.3) combined with two-universal input/output hashing for `1`-bit shrinkage ([`CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/EntropyReduction.lean), Lemmas 5.4 and 5.5) then yield [`AdversaryInaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), [`InaccessibleEntropyFamily.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean), and [`OneWay.exists_shrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (Section 5.1.5, Theorem 5.1, STEPS 1–3): because neither `shrunkHashEscapeInverter` nor `repEscapeInverter` reads the candidate index, each grid adversary `B` induces one strict-PPT base adversary whose Definition 3.9 accessible-set family selects a collision-resistant candidate sequence `goodIdx` in [`ShrinkingCollisionGrid`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/Amplify.lean) (`exists_good_candidate`). Although `goodIdx` depends on the adversary and need not be efficiently computable, [`rompelCompression`](../../CslibFrontier/Crypto/Computational/InaccessibleEntropy/TargetCollision.lean) evaluates all `gridCount n` candidates uniformly across `rompelCascadeSteps G n = (2 * gridCount n - 1) * outLen n` XOR-masked `1`-bit shrinking steps under one shared `rompelCascadeSteps G n * inLen n`-bit step-key sequence and concatenates their outputs (`2 * (gridCount n * outLen n) → gridCount n * outLen n`; adapting [hhrvw20][hhrvw20] Section 5.1.4, Lemmas 5.6–5.7, pp. 29–30, and Section 5.1.5, STEP 4, p. 31, and STEP 5(ii–iii), p. 32, using one fresh `inLen n`-bit subkey per `1`-bit step and sharing that sequence across candidates rather than claiming Lemma 5.7's `O(|y| log t)` compact-key bound or STEP 5(iii)'s per-candidate keys; the compact keys remain open in [#4821](https://github.com/cslib-community/cslib-frontier/issues/4821)), with single-stage planted-subkey reduction `rompelCompressionInverter` (which likewise guesses `(qGuess, slot)` without reading `goodIdx`) achieving exact key simulation at multiplicative loss `dyadicSize (gridCount n) * dyadicSize (rompelCascadeSteps G n)` and zero additive error (`ShrinkingCollisionGrid.targetCollisionResistant_rompelCompression`, `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantCompression`, `OneWay.exists_targetCollisionResistant_keyedCompressionFamily`). Composing with `KeyedCompressionFamily.treeHash` yields `rompelHash`, `AdversaryInaccessibleEntropyFamily.exists_targetCollisionResistantHash`, and `OneWay.exists_targetCollisionResistant_keyedHashFamily` ([rompel90][rompel90]; [hhrvw20][hhrvw20] Section 5.1, Theorem 5.1, p. 26), with concrete checks in [`CslibFrontierTests/Crypto/InaccessibleEntropy.lean`](../../CslibFrontierTests/Crypto/InaccessibleEntropy.lean) and [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean).

The negacyclic ring `R[X]/(X^n + 1)` on coefficient vectors lives in
[`Foundations/Algebra/Negacyclic.lean`](../../CslibFrontier/Foundations/Algebra/Negacyclic.lean),
independently of any cryptographic definition. It provides the coefficient-vector operations
`rotMatrix`, `negacyclicMul` and `innerPoly` together with their algebra and coefficient
bounds, and the typed ring `Negacyclic R n`: a one-field structure around `coeffs : Fin n → R`
whose `*` is `negacyclicMul`, a commutative ring and `R`-algebra for commutative `R`. It
represents the quotient for `n ≠ 0`; at `n = 0` it is the zero ring, a chosen zero-dimensional
extension, since the quotient there is `R[X]/(2)`.
`Negacyclic` is a structure rather than a synonym for `Fin n → R`, so the pointwise product of
the function type cannot be used by mistake. Move between the two views with `ofCoeffs`,
`coeffs` and `coeffsLinearEquiv`; `coeffs_mul` and `ofCoeffs_innerPoly` translate products and
inner products. The [checked examples](../../CslibFrontierTests/Foundations/Algebra/Negacyclic.lean)
include `X^4 = -1` over `ZMod 7` and dimension zero, where `1 = 0`.

The polynomial interpretation is proved in
[`SIS/Polynomial.lean`](../../CslibFrontier/Crypto/Computational/SIS/Polynomial.lean).
For `n ≠ 0` and a nontrivial commutative ring `R`, `negacyclicEquiv` is an `R`-algebra
equivalence `Negacyclic R n ≃ₐ[R] AdjoinRoot (X^n + 1)`, so `map_mul` carries
negacyclic multiplication to quotient multiplication and injectivity reflects quotient equalities
back to coefficient vectors. In
[`SIS/Module.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module.lean),
`ofCoeffs_comp_moduleSISMap` reads the existing Module-SIS map as a matrix-vector product over
`Negacyclic (ZMod q) n` and `moduleSISMap_eq_zero_iff` restates its zero equation there; neither
needs the quotient. `negacyclicEquiv_mulVec` then carries any such product entrywise to the
quotient ring. The checked examples in
[`NegacyclicPolynomial.lean`](../../CslibFrontierTests/Crypto/NegacyclicPolynomial.lean) include
integers, composite modulus `6`, characteristic `2`, dimension `1`, and reflection of the
Module-SIS zero equation. Dimension zero is excluded because its quotient is `R[X]/(2)`, while
`Negacyclic R 0` is the zero ring. This algebraic bridge adds no hardness or runtime claim.

The pure coefficient identity `negacyclicMul_eq_coeff_mul` is available separately in
[SIS/Polynomial/Coefficients.lean](../../CslibFrontier/Crypto/Computational/SIS/Polynomial/Coefficients.lean),
so algebra clients need not import native computation certificates. For native multiplication, import
[SIS/Native.lean](../../CslibFrontier/Crypto/Computational/SIS/Native.lean).
`negacyclicMulResidues n q a b` truncates two natural-coefficient lists to `n`, computes the
existing integer `mulZJet (2*n)`, and reduces each lower coefficient minus its wrapped upper
coefficient modulo `q`. Short lists are zero-padded and the output has exactly `n` entries.
The plain certificate charges unary `n`, binary `q`, and both complete framed binary input
lists. It imposes no coefficient-size bound. For `q > 0`, `negacyclicMulResidues_ofFn` identifies
the output with the canonical coefficients of the existing `negacyclicMul`; neither primality
nor positive dimension is needed. At `q = 0`, the total operation instead truncates each
signed result at zero, with no canonical-residue interpretation claimed.
The [checked clients](../../CslibFrontierTests/Crypto/NegacyclicNative.lean) include `X² = -1`
modulo six, modulus one, empty and irregular inputs, a 128-bit modulus, and the actual
rank-one `moduleLWEKeyGen` coefficient computation. Full native encryption, seed codecs and
small-secret security still remain separate obligations. This arithmetic certificate does not
remove the existing restrictions on exact native samplers or imply small-secret security.

Plain-LWE bit encryption at modulus `2 ^ w` is formalized in [`LWE/Regev.lean`](../../CslibFrontier/Crypto/Computational/LWE/Regev.lean) and [`LWE/Regev/Security.lean`](../../CslibFrontier/Crypto/Computational/LWE/Regev/Security.lean) (checked in [`CslibFrontierTests/Crypto/Regev.lean`](../../CslibFrontierTests/Crypto/Regev.lean)). Primal Regev encryption (`Regev.encryptWithCoins`, `Regev.decrypt`) uses a noisy LWE public key and binary subset-sum encryption coins `xᵀ A + (μ * 2 ^ (w - 1), 0, …, 0)`, giving zero-error worst-case decryption when key-generation errors are bounded entrywise in `Int.natAbs` by `η` with `4 * (m * η) < 2 ^ w` (`Regev.decrypt_encryptWithCoins`, `Regev.keyGen_encrypt_correct`). On serialized secret keys and ciphertexts (`LWE.serializeSecret`, `Regev.serializeCiphertext`), `Regev.decryptSerialized` (built on the shared residue threshold `LWE.decodeResidue` in [`LWE/Decoding.lean`](../../CslibFrontier/Crypto/Computational/LWE/Decoding.lean) and modular inner product `LWE.secretProductResidue` in [`LWE/KeyGen.lean`](../../CslibFrontier/Crypto/Computational/LWE/KeyGen.lean), with `LWE.decodeResidue` also reused by `DualRegev.decryptSerialized` and both reused by `GSW.decryptSerialized`) computes `Regev.decrypt` in polynomial time (`Regev.decryptSerialized_serialize`, `Regev.keyGenSerialized_encryptSerialized_correct`, `Regev.computableInPolyTime_decryptSerialized`). For the shared serialized LWE key generator `LWE.keyGenSerialized` and `Regev.encryptSerialized`, `Regev.indCPA_of_decisionLWE` proves native single-challenge `Encryption.INDCPA` for polynomial-time schedules `n`, `m`, `w` satisfying eventually `(n + 1) * w + 2 * security ≤ m` under `DecisionLWE` for the centered-binomial law `LWE.noiseLaw (w k) (η k)`, via the concrete bound `Regev.advantage_game_le` (at most `2` times the advantage of the uniform PPT reduction `Regev.lweDistinguisher` plus `Regev.hidingError = √(2 ^ ((n + 1) * w) / 2 ^ m)`). The statistical step is typed: `Regev.challengeGame keys A b` is `Game.withSetup keys` of the shared `lrExperiment` with Regev encryption, played by a `TwoStage` adversary `A` on public matrices and ciphertexts, and `Regev.challengeGame_uniform_advantage_le` bounds it under a uniform matrix; `Regev.publicKeyGame_uniformEnsemble` identifies the word experiment with the one played by `Regev.typedAdversary`, which reads both inputs through their canonical encodings. For adaptive `Q`-query left-or-right attacks, `Regev.lorGame_uniform_advantage_le` and `Regev.lorGame_advantage_le` bound the typed game `Regev.lorGame` via `Regev.lorDistinguisher`, while [`Encryption/LoRCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/LoRCPA.lean) (`Encryption.LoRAdversary`, `Encryption.lorDistinguisher`, `Encryption.lorKeyDistinguisher`, `Encryption.lorGame`, `Encryption.LoRINDCPA`) together with `Regev.lorDistinguisherSerialized`, `Regev.lorLweDistinguisher`, and `Regev.lorGameSerialized` provide the uniform strict-PPT multi-challenge reduction (`Regev.isPPT_lorLweDistinguisher`, `Regev.lorGameSerialized_advantage_le`, `Regev.lorIndCPA_of_decisionLWE`).

[`LWE/DualRegev.lean`](../../CslibFrontier/Crypto/Computational/LWE/DualRegev.lean) formalizes Gentry–Peikert–Vaikuntanathan's plain-LWE dual scheme at modulus `2 ^ w`: a short integer secret `e`, the noiseless syndrome public key `(A, eᵀ A)`, and LWE-style noisy encryption `(A s + x, ⟨u, s⟩ + x₀ + μ * 2 ^ (w - 1))` (contrasting with primal Regev's noisy public key and binary subset-sum coins, and with `moduleLWEKeyGen` / `moduleLWEEncrypt` in [`SIS/ModuleEncryption.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean), whose public key `(A, A s + e)` is itself a noisy Module-LWE sample over `ℤ_q[X]/(X^n+1)`). With secret entries bounded in `Int.natAbs` by `β` and encryption errors bounded by `η`, `DualRegev.decrypt_encryptWithCoins` proves zero-error decryption when `4 * (m * β * η + η) < 2 ^ w`; for generated binary secrets (`β = 1`), `DualRegev.keyGen_encrypt_correct` requires `4 * (m * η + η) < 2 ^ w`, and for trapdoor-extracted keys under the support-only preimage condition `DualRegev.GPVTrapdoor.SamplesShortPreimages`, `DualRegev.GPVTrapdoor.decrypt_encryptWithCoins_extract` establishes decryption correctness. On serialized binary secrets (`DualRegev.serializeSecret`) and ciphertexts (`DualRegev.serializeCiphertext`), `DualRegev.decryptSerialized` (reusing `LWE.decodeResidue`) computes `DualRegev.decrypt` in polynomial time (`DualRegev.decryptSerialized_serialize`, `DualRegev.keyGenSerialized_encryptSerialized_correct`, `DualRegev.computableInPolyTime_decryptSerialized`). `DualRegev.dist_keyGen_uniform_le` bounds the statistical distance of the binary-secret public key from uniform; in [`LWE/DualRegev/Security.lean`](../../CslibFrontier/Crypto/Computational/LWE/DualRegev/Security.lean), `DualRegev.indCPA_of_decisionLWE` establishes native single-challenge `Encryption.INDCPA` for `DualRegev.keyGenSerialized` and `DualRegev.encryptSerialized` under `(m + 1)`-sample `DecisionLWE` for `LWE.noiseLaw` when polynomial-time schedules eventually satisfy `w * n + 2 * security ≤ m` (via `DualRegev.advantage_game_le`, checked in [`CslibFrontierTests/Crypto/Regev.lean`](../../CslibFrontierTests/Crypto/Regev.lean)).

Micciancio–Peikert gadget-based lattice trapdoors over `ZMod (2 ^ w)` (IACR ePrint 2011/501, Sections 4–5) are in [`LWE/Trapdoor/Gadget.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Gadget.lean) and [`LWE/Trapdoor/Basic.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor/Basic.lean) (re-exported by [`LWE/Trapdoor.lean`](../../CslibFrontier/Crypto/Computational/LWE/Trapdoor.lean) and checked in [`CslibFrontierTests/Crypto/Computational/LWE/Trapdoor.lean`](../../CslibFrontierTests/Crypto/Computational/LWE/Trapdoor.lean)). `Gadget.lean` connects the power-of-two gadget matrix `gadgetMatrix w` (`G = I_ι ⊗ gᵀ`) to `GSW.bitCompose` and `GSW.powersOfTwo` (`gadgetMatrix_mulVec`, `vecMul_gadgetMatrix`), proves that binary decomposition is a right inverse, `G *ᵥ gadgetDecomp w u = u`, so `G` is primitive (`gadgetMatrix_mul_gadgetDecompMatrix`, `gadgetMatrix_surjective`), shows that `scalarBasis w` (`S_w`) has determinant `2 ^ w` (`det_scalarBasis`) and that the columns of `S_w` and of the block matrix `gadgetBasis w` (`S = I_ι ⊗ S_w`) lie in `Λ^⊥(gᵀ)` and `Λ^⊥(G)` respectively with entries at most `2` and squared column length at most `5` (`gadgetVector_vecMul_scalarBasis`, `gadgetMatrix_mul_gadgetBasis`, `sum_sq_scalarBasis_col_le_five`, `sum_sq_gadgetBasis_col_le_five`; Proposition 4.2), and proves that the iterative inversion of Section 4.1 recovers `s` from `sᵀ G + eᵀ` whenever `4 * |e p| < 2 ^ w` (`invertScalar_correct`, `invertGadget_gadgetLWE`). `Basic.lean` defines the tagged matrix `taggedMatrix w Abar R H = [Abar | H * G - Abar * R]` of Algorithm 1, proves the unrestricted tag identity `A * [R; I] = H * G` (`taggedMatrix_mul_trapdoorTransform`), and defines `IsHTagTrapdoor` requiring both `A * [R; I] = H * G` and an invertible tag `IsUnit H` as in Definition 5.2 (`isHTagTrapdoor_taggedMatrix`, `isHTagTrapdoor_untaggedMatrix`, `IsHTagTrapdoor.surjective`). It lifts binary gadget preimages to short preimages under `A` (`taggedMatrix_mulVec_invertSyndrome`) and lifts `S` to the kernel vectors `[R; I] * S` of `A`, the right-hand block of the basis in Lemma 5.3 (`taggedMatrix_mul_extendedGadgetBasis`). For Algorithm 2, it proves recovery of `s` whenever the projected error `e_1ᵀ R + e_2ᵀ` has every coordinate below `2 ^ w / 4` (`invertLWESecret_trapdoorLWE`), exact recovery of `(s, e)` when in addition every original error coordinate satisfies `2 * |e k| < 2 ^ w` (`invertLWE_trapdoorLWE`), and both from the entrywise bound `4 * (1 + |μ| * B_R) * B_e < 2 ^ w` (`invertLWE_trapdoorLWE_of_norm_bound`), the deterministic part of Theorem 5.4 with infinity-norm hypotheses. `genTrap` samples Algorithm 1 with centered-binomial `R` (`mem_support_genTrap`), and in the idealized hybrid `genTrapIdeal`, where `Abar * R` is replaced by a uniform block, the public matrix is exactly uniform for every tag (`eval_genTrapIdeal_eq_uniform`). Not formalized: the step from `genTrap` to `genTrapIdeal` (regularity or decision-LWE), so the near-uniformity of `A` in Theorem 5.1 is not proved; the basis property of `S_w` and the full basis of Lemma 5.3; the Gaussian-error claim of Theorem 5.4; non-power-of-two moduli; and discrete-Gaussian preimage sampling and delegation (Sections 5.4–5.5).

ML-DSA (CRYSTALS-Dilithium) is in [`MLDSA/Decompose.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Decompose.lean),
[`MLDSA/Hint.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Hint.lean),
[`MLDSA/Basic.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Basic.lean) and
[`MLDSA/KeyOnly.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/KeyOnly.lean), with the
compressed-verification reduction in
[`MLDSA/CompressedKeyOnly.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/CompressedKeyOnly.lean)
and bounded compressed signing in
[`MLDSA/Signing.lean`](../../CslibFrontier/Crypto/Computational/MLDSA/Signing.lean).
`power2Round` follows FIPS 204 Algorithm 35; `power2RoundVec_reconstruct` and
`abs_power2RoundVec_low_le` give the coefficientwise public-key identity and low-part bound used by
the Dilithium self-target calculation. `decompose`, `highBits` and `lowBits` follow the commitment
rounding with its `q - 1` wrap-around rule; the reusable facts are uniqueness of the decomposition
(`decompose_intCast_mul_add`) and stability of the high bits under `β`-short perturbations
(`highBits_add_of_abs_lowBits_lt`). `makeHint` and `useHint` follow FIPS 204 Algorithms 39 and 40;
`useHint_makeHint` proves Dilithium's short-correction recovery law, `useHint_injective` separates
the two hint bits, and `useHint_lt` states NIST's proposed corrected strict output range.
`hintResidual`, `useHint_mul_eq_add_hintResidual` and `abs_hintResidual_valMinAbs_le` formalize the
arbitrary-hint identity and `2γ₂ + 1` bound of Dilithium v3.1 Lemma 1(2); the stronger sparse-hint
conclusion remains open.
`signAttempt`,
`sign` and `verify` model the uncompressed-public-key scheme with an arbitrary hash-to-ball
function and mask sampler (it does not use the Power2Round or hint layers, byte encodings or seed
expansion), and
`verify_sign` proves correctness under `Params.Valid`, which the three standard parameter sets
satisfy. `succProbability_koaGame_le` bounds key-only forgery by the Module-LWE advantage
`ModuleLWE.advantage` of `forgeryDistinguisher` for the short secret and error laws plus the
self-target MSIS success of `selfTargetReduction`;
chosen-message security, which needs signing-oracle simulation in the random-oracle model, is not
formalized. The separate compressed surface computes `t₁` and `t₀` from the full semantic public
vector `t`, verifies `H(UseHint(h, A z - c t₁ 2ᵈ), M) = c`, and proves the source's equations
(9)--(12): every verifying key-only forgery gives a self-target solution at radius
`max (γ₁ - β) (2γ₂ + 1 + τ 2^(d-1))`. Its explicit Module-LWE distinguisher and self-target solver
give the analogous finite-game key-only bound. This is not a chosen-message, strong-unforgeability,
asymptotic-negligibility or concrete ML-DSA-44/65/87 security theorem. The latter endpoints still
need the corrected transform losses, failure and query terms, exact assumption parameters, and
resource translations under an explicit coding convention. Those translations charge the encoded
description size of each `B(A)`, time, space, randomness and queries, plus its actual online
wrapper, controller, advice, layout, copying and interpreter costs. Offline `A ↦ B(A)` compiler
time is not attack time unless the produced reduction executes that compiler.

The bounded compressed signer follows Algorithm 7's two rejection stages, including
`||c t₀||∞ < γ₂` and the hint-weight bound, and uses the explicit counter schedule
`κ + i ℓ`. Exhaustion returns one `none` result; this is executable functional semantics, not a
model of the standard's physical destruction of intermediate state or side-channel behavior.
`signAttempt_eq_some_of_compressedSignAttempt_eq_some` connects every accepted compressed attempt
to the existing uncompressed signer. Under `Params.Valid`, `4 * γ₂ < q`, a hash whose outputs lie
in `B_τ`, and the secret-key bound `||s₂||∞ ≤ η`,
`compressedVerify_compressedSignAttempt` proves that every accepted attempt passes the compressed
verifier; `compressedVerify_compressedSignBounded` lifts this to the bounded loop. The proof uses
`compressedVerifierCommitment_eq_verifierCommitment_add_lowPart` to identify the verifier's
commitment with the uncompressed commitment plus `c t₀`, then applies the `MakeHint`/`UseHint`
recovery theorem. The explicit mask schedule is not identified with seeded `ExpandMask`.
Published FIPS 204 Appendix C, Table 3 gives `814` as the minimum bounded-signing limit under the
standard's stated distribution assumptions. The numeral alone proves no failure bound in the
semantic model, and this module formalizes no replacement limit.

The [checked examples](../../CslibFrontierTests/Crypto/MLDSA.lean) cover the
Power2Round tie and high-end boundaries, the Decompose wrap-around case, and a toy instance that
signs, verifies, rejects a modified response and yields a self-target solution. The
[hint client](../../CslibFrontierTests/Crypto/MLDSAHint.lean) covers both standardized `γ₂`
families and positive, negative and wrap-around bucket adjustments. The
[compressed client](../../CslibFrontierTests/Crypto/MLDSACompressedKeyOnly.lean) uses the
ML-DSA-44 coefficient dimensions, exercises set and clear hints and a nonzero `Power2Round` low
part, checks the exact self-target identity, and rejects after changing the hash-checked hint.
The [bounded-signing client](../../CslibFrontierTests/Crypto/MLDSASigning.lean) separates
first-stage, product-norm and hint-weight rejection, checks counter-stepped first-success and
exhaustion, and checks both the compressed/uncompressed attempt bridge and compressed-verification
correctness on a nonvacuous valid one-coefficient instance.

The SLH-DSA address-domain layer from FIPS 205 ([fips205][fips205]) is in
[`SLHDSA/Address.lean`](../../CslibFrontier/Crypto/Primitives/SLHDSA/Address.lean), with checked
layouts in [`SLHDSAAddress.lean`](../../CslibFrontierTests/Crypto/SLHDSAAddress.lean).
`Address.toBits` serializes the common layer and tree fields, the seven-valued address type and the
three type-dependent words as the standard's canonical 32-byte big-endian address;
`Address.toBytes` exposes the same layout as a typed `FixedBytes 32` value.
`Address.setTypeAndClear` preserves the common fields while clearing all final 12 bytes, and the
seven typed constructors satisfy the padding, fixed-layer and fixed-height requirements in
Figures 3–9. `Address.toCompressedBits` is literally the byte-slice projection of Figure 18 used
by the SHA2 parameter sets, and `Address.toCompressedBytes` gives its typed 22-byte form. The
compressed projection is injective under `Address.FitsCompressed`, which records that the
one-byte layer and eight-byte tree fields do not overflow. The unrestricted compressed format is
not injective, and the checked client exhibits the discarded high tree word. This module does not
define the FIPS 205 hash instantiations, WOTS+, XMSS, FORS, the hypertree, signing or verification,
nor does it prove classical or quantum security.

FIPS 202 SHAKE256 and SHAKE128 ([fips202][fips202]) are implemented in
[`Hash/Keccak.lean`](../../CslibFrontier/Crypto/Primitives/Hash/Keccak.lean) and
[`Hash/Keccak/SHAKE128.lean`](../../CslibFrontier/Crypto/Primitives/Hash/Keccak/SHAKE128.lean) on
top of the existing generic sponge mechanics. The executable state uses 25 lanes in `5 * y + x`
order and shares the standard's θ/ρ/π/χ/ι maps and 24-round permutation. `Keccak.shake256` uses the
1088-bit rate and 512-bit capacity, while `Keccak.shake128` uses the 1344-bit rate and 256-bit
capacity; both use the `1111` suffix, `pad10*1` and explicit least-significant-bit-first bytes. The
byte/state views are proved inverse, and `take_shake256` and `take_shake128` prove prefix
consistency. The [SHAKE256 client](../../CslibFrontierTests/Crypto/Keccak.lean) checks NIST's 0-bit
and 1600-bit-message examples, both sides of its 136-byte rate boundary, and a Falcon-512 KAT
prefix. The [SHAKE128 client](../../CslibFrontierTests/Crypto/SHAKE128.lean) checks NIST's 0-bit
and 1600-bit-message examples, crosses its 168-byte rate boundary, and checks the prefix API.
These are executable specifications, not collision/preimage results, constant-time implementations
or FIPS validations.

The shared byte and SHA-2 boundary used by the FIPS 205 SHA2 parameter sets is in
[`ByteString.lean`](../../CslibFrontier/Crypto/Primitives/ByteString.lean) and
[`SHA2.lean`](../../CslibFrontier/Crypto/Primitives/Hash/SHA2.lean) [fips1804][fips1804].
`FixedBytes n` records digest lengths in the type, while Mathlib's `Fin.take` and `Fin.append`
provide typed truncation and concatenation. `sha256` and `sha512` are total executable functions;
`ValidSHA256Input` and `ValidSHA512Input` record FIPS 180-4's prescribed input-length domains.
Equal-length byte lists and their `bytesToBitsBE` serializations have the same lexicographic order
(`bytesToBitsBE_lt_iff_lt`).
The implementation follows the standard's byte-aligned padding, message schedule, compression and
digest conversion, but no independent functional-correctness theorem is claimed. The
[ordinary-import client](../../CslibFrontierTests/Crypto/SHA2.lean) checks NIST's official
one- and two-block SHA-256 and SHA-512 examples and both padding boundaries. This is reusable
executable infrastructure: it does not yet package FIPS 205's `F`, `H`, `T_l`, `PRF`, `PRF_msg` or
`H_msg` calls, and establishes neither asymptotic security nor concrete candidate-parameter
advantage, query, machine-resource or program-size bounds.

Falcon's current checked layer ([falcon2020][falcon2020]) is deliberately narrower than a security
theorem. Import
[`Falcon/Verification.lean`](../../CslibFrontier/Crypto/Computational/Falcon/Verification.lean) for
the NIST-selected Falcon Round 3 submission version 1.2's algebra after hashing and signature
decoding: `Falcon.reconstructFirst` computes the centered representative of `c - s₂h`,
`Falcon.pairSquaredNorm` computes `‖(s₁,s₂)‖²`, and
`Falcon.verify_of_signingRelation` proves acceptance of a centered, bounded relation witness.
Import
[`Falcon/VerificationFrontend.lean`](../../CslibFrontier/Crypto/Computational/Falcon/VerificationFrontend.lean)
for the v1.2 NIST signed-message frontend. `Falcon.parseNistSignedMessage` checks the two-byte
big-endian signature length, 40-byte salt, `0010nnnn` degree header and canonical compressed
`s₂`; `Falcon.hashToPointPrefix` applies Algorithm 3's big-endian 16-bit rejection rule to a
finite XOF output prefix; and `Falcon.verifyNistWithXof` injects exactly `salt ++ message` into a
caller-supplied prefix function before invoking the algebraic verifier. The
[ordinary-import client](../../CslibFrontierTests/Crypto/Falcon.lean) covers canonical and
malformed encodings, salt/message layout, rejection sampling, boundary acceptance, and compact
decoder/hash fixtures derived from the first official Falcon-512 NIST KAT. The SHAKE client above
now checks the concrete 20-byte prefix used by that fixture.

[`Falcon/BerExp.lean`](../../CslibFrontier/Crypto/Computational/Falcon/BerExp.lean) isolates
Algorithm 14's exact distributional threshold step after its floating-point approximation has
already produced `z : Fin (2^64)`. `Falcon.berExpThresholdCoin` applies the public deterministic
strict comparison to a sample from the shared fixed 64-fair-bit sampler, and
`Falcon.eval_berExpThresholdCoin_true` proves acceptance mass exactly `z / 2^64`.
The [ordinary-import client](../../CslibFrontierTests/Crypto/FalconBerExp.lean) checks the strict
comparison and the thresholds zero, one, one half and `2^64 - 1`. This denotational interface does
not itself model the reference implementation's byte-consumption trace.

[`Falcon/BerExpLazy.lean`](../../CslibFrontier/Crypto/Computational/Falcon/BerExpLazy.lean)
formalizes Algorithm 14, lines 5--10, as the actual sequential lazy comparison. It uses the shared
`Byte` type and `natToFixedBytesBE` for `z`, draws eight fair bits for each visited byte, stops at
the first mismatch, and returns the decision, number of bytes read and source ledger. The ledger
charges one byte draw, source subtraction and loop equality test per consumed byte, exactly
`8 * bytesRead` fair bits, and no external oracle or handler. Its comparison coordinate excludes
the one final sign extraction and loop-index tests. The deterministic trace compares byte lists
lexicographically; `Falcon.berExpLazyTrace64_accepted` connects that comparison to the
same strict 64-bit threshold predicate, and `Falcon.eval_berExpLazyCoin_accepted` proves equality
of the complete decision distributions. The trace consumes between one and eight bytes, consumes
all eight and rejects when every byte agrees, and reads past the first byte with exact probability
`2^-8`. The [ordinary-import client](../../CslibFrontierTests/Crypto/FalconBerExpLazy.lean) checks
first- and later-mismatch decisions, the eight-byte boundary, all-equal rejection, the 64-bit
bridge, exact laws and resource fields. These source operations are not Lean or native steps.
This layer does not model PRNG-buffer refills, bound `ApproxExp`'s floating-point error, construct
`BaseSampler` or `SamplerZ`, prove a Gaussian or retry law, or certify native runtime, circuit,
query or static-program size.

The Falcon frontend deliberately retains a finite XOF-prefix boundary: the concrete SHAKE function
can supply any requested finite prefix, but the frontend does not choose a universally sufficient
length for rejection sampling. Full KAT verification, public-key decoding, NTRU key generation,
FFT/NTT correctness, the rest of the adaptive Gaussian trapdoor sampler and its distribution,
termination and rejection analysis, average-case NTRU-SIS, ROM/QROM reductions, certified
efficiency, and reconciliation with the still-developing FIPS 206 remain separate obligations.

The source-faithful SLH-DSA WOTS+ digit preprocessing from FIPS 205 is in
[`SLHDSA/WOTS/Digits.lean`](../../CslibFrontier/Crypto/Primitives/SLHDSA/WOTS/Digits.lean), with
edge checks in [`SLHDSAWOTSDigits.lean`](../../CslibFrontierTests/Crypto/SLHDSAWOTSDigits.lean)
[fips205][fips205]. `base2b` is Algorithm 4's big-endian byte-to-base conversion. For the three
standard values `n = 16, 24, 32`, `WOTS.digits` implements the common first seven lines of
`wots_sign` and `wots_pkFromSig`: the `2n` base-16 message digits followed by the three complement
checksum digits, including the specified four-bit left shift and two-byte encoding. The client now
uses the same `Byte` and `bytesToBitsBE` boundary as SHA-2 rather than a parallel serialization.
This milestone
does not define the WOTS+ hash chain, key generation, signing, public-key reconstruction, concrete
FIPS 205 hash instantiations, or any security reduction; those remain obligations under the NIST
post-quantum portfolio roadmap item.

These are implications from hardness assumptions. They do not prove that a concrete OWF, DDH group, LWE family or SIS parameter choice is hard. `DecisionLWE` runs the fixed-instance experiments `LWE.realExperiment` and `LWE.randomExperiment` over `ZMod (2 ^ w)`: a typed distinguisher receives a uniform matrix `A` and either `A t + e`, with independent errors and one shared uniform secret, or an independent uniform vector. For other secret and error laws over any finite commutative ring, `LWE.advantage` is the distance between `LWE.realGame` and `LWE.randomGame`. The distinguisher's machine reads only the row-major binary word of `[b | A]`, and `decisionLWE_iff_encoded` shows that this is the word-level assumption on the serialized public matrix `[B*t+e | B]` (checked in [`CslibFrontierTests/Crypto/DecisionLWE.lean`](../../CslibFrontierTests/Crypto/DecisionLWE.lean)); in [`SIS/Module.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module.lean), `expandModuleMatrix` and `flattenPolyVec` embed negacyclic `ModuleSIS` and `ModuleLWE` instances over `ℤ_q[X]/(X^n+1)` into unstructured `(d * n) × (k * n)` matrices over `ℤ_q` (checked with concrete evaluations and nonvacuity proofs in [`CslibFrontierTests/Crypto/ModuleSIS.lean`](../../CslibFrontierTests/Crypto/ModuleSIS.lean)); [`LWE/Module.lean`](../../CslibFrontier/Crypto/Computational/LWE/Module.lean) states decision Module-LWE as the typed games `ModuleLWE.realGame` and `ModuleLWE.randomGame` for any secret and error laws, whose advantage `ModuleLWE.advantage` is the LWE advantage over the ring `Negacyclic (ZMod q) n` (`ModuleLWE.advantage_eq_lweAdvantage`), and the assumption `DecisionModuleLWEWith` takes an explicit secret law and error law, as the CRYSTALS-Kyber and CRYSTALS-Dilithium submissions state Module-LWE with short secrets, and is the word-level assumption by `decisionModuleLWEWith_iff_encoded`; it is meaningful only for a parameter family that grows with the security parameter, and `DecisionModuleLWE` is its uniform-secret case (checked in [`CslibFrontierTests/Crypto/DecisionModuleLWE.lean`](../../CslibFrontierTests/Crypto/DecisionModuleLWE.lean)); and [`SIS/ModuleEncryption.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption.lean) builds Module-LWE public-key encryption (`moduleLWEKeyGen`, `moduleLWEEncrypt`, `moduleLWEDecrypt`), bounded-noise decryption correctness (`moduleLWEDecrypt_moduleLWEEncrypt_eq`), and two-hop public-key/ciphertext reductions to `ModuleLWE.sampleLaw` (`advantage_realEncryptionView_uniform_le`, `advantage_realEncryptionView_msg_le`, checked in [`CslibFrontierTests/Crypto/ModuleEncryption.lean`](../../CslibFrontierTests/Crypto/ModuleEncryption.lean)); no worst-case lattice reduction is asserted there.

For deterministic native key generation, import
[`ModuleEncryption/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Native.lean).
`exists_computableInPolyTime_moduleLWEKeyGen` supplies one total word function with a plain
polynomial-time certificate and exact agreement with `ModuleLWE.encodeSample (moduleLWEKeyGen …)`.
Both rank and polynomial degree are unary inputs; the positive modulus and signed secret/error
coefficients are binary. The public matrix input uses `ModuleSIS.encodeMatrix`: its structured
`(k*n)`-square rotation-block expansion is already present. Runtime charges that complete matrix
word, both complete framed signed lists and the dimensions; it does not assume a seed codec.
The implementation reuses total framing/number decoders and the upstream padded list dot product,
then reduces each integer coordinate modulo `q`. Short rows/vectors pad with zero and excess
entries are ignored, but still contribute to input length. Canonical equality requires `q > 0`;
there is no assertion that malformed words are rejected. [Checked clients](../../CslibFrontierTests/Crypto/ModuleKeyGenNative.lean)
use the same certified function for rank two, degree two, composite modulus six, signed wraps,
modulus one, zero dimensions and a 129-bit modulus. The structured matrix sampler below supplies
its public matrix input, and the joint sampler below composes the actual secret/error samplers.
Full native encryption, seed compression and security remain separate obligations.

For deterministic native decryption, `exists_computableInPolyTime_moduleLWEDecrypt` in
[`ModuleEncryption/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Native.lean)
supplies one total word function with a plain polynomial-time certificate and exact agreement with
`List.ofFn (moduleLWEDecrypt …)`. Unary rank `k`, unary degree `n`, and binary modulus `q` are
runtime inputs; secret coordinates use `ModuleSIS.encodeVec` over signed integers, and the ciphertext
uses `SIS.encodeMatrix (extendCiphertext ct)`. Decryption evaluates each secret polynomial's
canonical residues modulo `q`, performs negacyclic multiplication against each ciphertext polynomial
using the certified integer negacyclic engine, sums polynomial columns, and applies centered threshold
decoding `decodePolyMsg` on canonical natural coefficients. The private implementation pads missing
coefficients and rows with zero, ignores excess entries while charging their input length, and at
modulus zero or on incomplete framing remains total without asserting quotient-ring semantics.
In-source checks and [checked clients](../../CslibFrontierTests/Crypto/ModuleEncryptionNative.lean) verify
honest Ring-LWE and Module-LWE encryption/decryption, rank zero, degree zero, modulus zero, modulus
one, incomplete framing, and threshold edge cases where residue differences of `q / 4` and `q / 4 + 1`
decode to `false` and `true`. Full native encryption, seed codecs, and security reductions under native
sampling remain separate obligations.

The structured matrix input itself now has a native constructor and exact sampler in
[`SIS/Module/MatrixSampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module/MatrixSampling.lean).
`exists_computableInPolyTime_encodeModuleMatrix` supplies one total implementation of the existing
`ModuleSIS.encodeMatrix`, from rectangular nested coefficient lists, unary row/rank/degree and a
binary modulus. Its canonical identity assumes `q > 0`; zero dimensions and modulus one are
included. The private implementation pads missing coefficients with zero, ignores excess entries
while charging their input length, and uses the actual negative wrap of `rotMatrix`. At modulus
zero it remains total, without a canonical residue interpretation.
`exists_isPPTOn_sampleEncodedModuleMatrix` samples independent polynomial coefficients using
`sampleBinaryNat w`, then performs that certified expansion. Its exact law is uniform on the
original polynomial matrix over `ZMod (2 ^ w)` followed by `ModuleSIS.encodeMatrix`, for unary
dimensions and bit width, including width zero. The expanded scalar entries are correlated. [Tests](../../CslibFrontierTests/Crypto/ModuleMatrixSampling.lean)
check a rectangular modulus-six expansion, empty shapes, a 129-bit modulus, and a nonrotation
matrix with zero structured-sampler mass but positive independent-scalar-uniform mass. They also
compose the same obtained sampler with the native key generator: the composition is strict PPT
for runtime dimensions/width and complete supplied signed secret/error words, and its concrete
conditional law agrees with the existing key generator. The joint sampler below supplies the
random secret and error, and deterministic native decryption is certified above by
`exists_computableInPolyTime_moduleLWEDecrypt`; native encryption, seed codecs and security
remain separate tasks.

For arbitrary positive binary moduli, including primes, import
[`Module/ApproximateSampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/Module/ApproximateSampling.lean).
`exists_isPPTOn_approximateEncodedModuleMatrix` gives one strict-PPT program using the existing
`sampleModNat width q` independently on each polynomial coefficient, then the same native
rotation-block expansion. Its exact law is the nested product of those actual residue laws
followed by `ModuleSIS.encodeMatrix`. Its all-event `CloseTo` error against the ideal structured
uniform law is at most `d*k*n*q/2^width`. The count is the number of independent polynomial
coefficients; expanded scalar entries remain correlated. The modulus is binary, dimensions and
width unary, and the program is total even at modulus zero, outside the positive-modulus law.
`exists_isPPTOn_sampleEncodedModuleMatrixWithPrecision` computes width `q.size + precision`
natively and gives error at most `d*k*n/2^precision`, with unary precision and binary modulus.
Neither theorem asserts exact uniform sampling for arbitrary moduli.

[Checked clients](../../CslibFrontierTests/Crypto/ModuleMatrixApproximation.lean) show that four fair
bits reduced modulo three give the encoded zero two-coefficient block mass `9/64`, whereas the
ideal structured law gives `1/9`. The bound is `3/8`. The same obtained sampler and native keygen
function compose uniformly on runtime dimensions, binary modulus and complete supplied secret
and error words; deterministic keygen postprocessing preserves that error against the existing
ideal conditional key law. Other clients cover width zero, modulus one, empty dimensions and a
129-bit modulus. The joint sampler below completes secret/error composition; native encryption
and security remain open.
The scalar all-event bridge `Probability.closeTo_uniform_sampleModNat` in
[`Game/CloseTo/UniformNat.lean`](../../CslibFrontier/Crypto/Game/CloseTo/UniformNat.lean) bounds the
sampled residue law against uniform `ZMod q` within `q / 2^width`. In the same module,
`Game.advantage_bind_sampleModNat_fin_le` and `Game.advantage_bind_sampleModNat_fin_fin_le` bound
the advantage lost when one or two uniform `Fin` draws are replaced by `sampleModNat` draws.

For full randomized key generation, import
[`ModuleEncryption/Sampling/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling/Native.lean).
`exists_isPPTOn_moduleLWEKeyGenJoint` supplies one native program before choosing rank `k`, degree
`n`, secret/error CBD widths, precision and modulus. It returns an ordinary pair of the existing
`ModuleSIS.encodeVec` signed-secret word and `ModuleLWE.encodeSample` public-key word. The secret
is the actual integer CBD draw; reducing its decoded coefficients modulo `q` gives exactly the
secret used to generate that public key, including when residues wrap. No no-wrap assumption or
additional secret codec is introduced. Dimensions, CBD widths and precision are unary runtime
inputs; the modulus is binary. The certificate charges all generated signed words, the full
expanded structured matrix, public output and framing.

The exact implemented joint law uses the existing CBD programs and bounded modular coefficient
sampler. Its all-event error from the ideal joint experiment is at most `k*k*n/2^precision`:
retain the same signed secret, then use `moduleLWEPublicKeyLaw` conditional on its residue and
with actual independent CBD polynomial errors. The theorem also bounds the public projection
against the existing generalized public-key law. Exact secret/error sampling adds no error to
the matrix bound. The program is total, with semantic claims requiring only `q > 0`.
[Checked clients](../../CslibFrontierTests/Crypto/ModuleKeyGenJoint.lean) use the same obtained witness
for a prime-three event with secret `-1`, matrix coefficient `1` and public coefficient `0`,
forcing nonzero error `1`. Its actual mass is `5/256` versus ideal `1/48`, a gap of `1/768`.
The same witness covers zero widths, modulus one, both empty shapes and a rank-two/degree-two
129-bit-modulus instance. These are key-sampling and execution statements (deterministic native
decryption is certified by `exists_computableInPolyTime_moduleLWEDecrypt`); native encryption, seed
codecs and small-secret security remain separate obligations.

The Module-LWE sampling APIs now accept explicit distributions: `moduleLWEPublicKeyLaw` has an
optional `secretLaw`, `encryptionViewOfKeyLaw` an optional `ephemeralLaw`, and `realEncryptionView`
accepts both. Their defaults remain uniform, and the existing security reductions concern those
uniform defaults. [`ModuleEncryption/Sampling.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling.lean)
proves that conditioning public-key generation on the actual sampled secret preserves the public
view, including when the same run retains `(secret, view)`. Sampling a fresh secret independently
of a public key would not preserve that correlation.
The concrete small-secret instance reuses the existing centered-binomial fair-bit program and
modular `LWE.noiseLaw`. Under `2*η < 2^w`, every sampled integer is its residue's centered lift,
so the resulting module secret satisfies the coefficient bound `η`. Nested list sampling has a
uniform strict-PPT certificate for unary row count, degree and binomial width, with binary signed
integer output. The subsequent modular-cast identity is semantic; this is not a native certificate
for the whole encryption scheme. [Tests](../../CslibFrontierTests/Crypto/ModuleEncryptionSampling.lean)
include nonzero supported secrets, zero dimensions/width, and a variable-row native client.
They also show that uniform rank-one, degree-one secrets and ephemeral values modulo sixteen,
with all errors one, decrypt a true message correctly with probability only `7/16`.
The existing deterministic correctness theorem requires bounded secrets as well as bounded noise;
this example does not contradict it. Small-secret security requires its own assumption and reduction;
the randomized correctness result below uses explicit support and noise-tail hypotheses.

For numerical modulus conversion, import
[`SIS/ModulusSwitch.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch.lean).
`moduleLWEModulusSwitch p ct` converts the existing ciphertext components with the reusable
[`ZMod.modulusSwitch`](../../CslibFrontier/Foundations/Data/ZMod/ModulusSwitch.lean): take
`valMinAbs`, multiply by the rational ratio `p / q`, round to the nearest integer with half
ties toward positive infinity, and reduce modulo `p`. It is not a ring homomorphism.
For `q,p > 0`, `exists_moduleLWEModulusSwitch_phase` supplies an integer representative of
the target phase whose distance from the scaled canonical source phase is at most
`(1 + ∑ j, ∑ l, |s j l|) / 2`. The secret at both moduli is the cast of the same integer
vector. The representative supplied at the target need not be its centered lift.
`exists_moduleLWEModulusSwitch_phase_of_lifts` exposes arbitrary integer lifts and their
carry equation; the canonical theorem constructs these carries automatically.
The [checked examples](../../CslibFrontierTests/Crypto/ModulusSwitch.lean) cover negative half
ties, composite moduli, modulus one, nonadditivity, and a ciphertext with nonzero carry.
This nearest-integer phase bound is original supporting algebra; it does not assert Boolean
plaintext preservation, parity-preserving switching, a security reduction, or a runtime bound.

For its native implementation, import
[`SIS/ModulusSwitch/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Native.lean).
`ZMod.modulusSwitchResidue q p x` computes the rounded integer by signed Euclidean division
`(2*p*x + q) / (2*q)`, then reduces it to a natural residue modulo `p`.
`modulusSwitchResidue_eq_val` identifies that result with the existing coefficient switch for
positive moduli, including negative half ties. The plain `intBin_roundScale` and
`ComputableInPolyTime.modulusSwitchResidue` certificates use binary `encNat` moduli and signed
binary `encIntBin` representatives; they reuse the existing signed division and remainder
certificates. `computableInPolyTime_modulusSwitchRows` lifts the implementation to arbitrary
runtime nested rows in `encList (encList encNat)`. Dimensions vary through the actual list
structure, and the polynomial bound counts the complete encoded input. The
`modulusSwitchRows_encodeMatrix_extendCiphertext` theorem identifies the output with
`SIS.encodeMatrix (extendCiphertext (moduleLWEModulusSwitch p ct))`, so there is no
separate ciphertext format. The [native tests](../../CslibFrontierTests/Crypto/ModulusSwitchNative.lean)
exercise a 128-bit modulus, negative representatives, modulus one, ragged/empty rows, the
existing ciphertext encoding, and composition of two certified conversions. This runtime
certificate adds no decoding or security guarantee.

For sufficient plaintext-preserving margins, import
[`SIS/ModulusSwitch/Correctness.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Correctness.lean).
Suppose the actual source phase is `encodePolyMsg q m + err`, with integer error bounded by
`Bq`, and use the same integer secret at both moduli. Write `S` for its coefficient absolute-value
sum and `Δ = |(p/q) * floor(q/2) - floor(p/2)|`. If
`(p/q) * Bq + (1+S)/2 + Δ ≤ Bp` and `4*Bp+2 < p`, then
`moduleLWEDecrypt_modulusSwitch_eq` proves that the switched ciphertext decrypts to `m`.
The source modulus need only be positive for that conclusion. The separate
`moduleLWEDecrypt_modulusSwitch_eq_source` adds `4*Bq+2 < q` to derive equality of the actual
source and target decryptions. These sufficient margins are not claimed optimal.
The error theorem constructs its target representative from the phase bound, including source
carries, rather than assuming a decoding conclusion. `moduleLWEDecrypt_modulusSwitch_encrypt_eq`
applies it to honest encryption using the existing integer error polynomial and centered secret.
The exact scale mismatch is zero for two even moduli, `1/2` for even source and odd target,
`p/(2*q)` for odd source and even target, and `|1-p/q|/2` for two odd moduli.
[Checked examples](../../CslibFrontierTests/Crypto/ModulusSwitchCorrectness.lean) apply the honest
encryption theorem in all four cases with nonzero noise, and exercise negative half ties and a
nonzero carry. They also show plaintext loss at target moduli one and two and failure at the
strict decoder threshold. This is deterministic correctness, with no additional security claim.

For randomized correctness, import
[`SIS/ModulusSwitch/Failure.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Failure.lean).
`toOuterMeasure_moduleLWEModulusSwitch_failure_le` uses the existing encryption view while
retaining the actual secret that generated the public key. Suppose the secret and ephemeral laws
are supported in centered coefficient bounds `Bs,Br`, and write `ν` for the polynomial-noise law.
Set `Q = k*n*Be*Br + k*n*Be*Bs + Be`. For positive source modulus `q`, target margin `4*Bp+2 < p`,
and `(p/q)*Q + (1+k*n*Bs)/2 + Δ ≤ Bp`, switched decryption fails with probability at most
`(2*k+1) * ν{e | e exceeds centered coefficient bound Be}`. The count is `k` key-error
polynomials, `k` encryption-error polynomials and one final polynomial, each sampled independently
as in the existing view. The proof reuses the deterministic theorem and the product-event union
bound; it assumes neither a decryption conclusion nor a source decoding margin.
[Checked clients](../../CslibFrontierTests/Crypto/ModulusSwitchFailure.lean) use the native
centered-binomial small-secret law for rank and degree one, switching from 32 to 16. Width-one
errors give zero failure. Width-two errors exceed good radius one with exact probability `1/8`,
giving an upper bound `3/8`; a supported error triple produces target phase 12 and proves positive
actual failure. These are original sufficient correctness bounds for the supplied laws. They add
no small-secret security reduction, Gaussian sampler or native certificate for the entire scheme.

For a concrete growing family, [ModulusSwitch/CenteredBinomial.lean](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/CenteredBinomial.lean)
sets `t = l+1`, rank and degree `t`, CBD1 secret/ephemeral coefficients, and CBD(8t) error
coefficients with good radius `4t`. Put `Q = 8t³+4t`, `Bp = floor((Q+t²+2)/2)`,
`w = Nat.size(4Bp+2)`, target `p = 2^w` and source `q = 2^(w+1)`.
The proved bounds are `p ≤ 68t³`, `q ≤ 136t³`, strict no-wrap `16t < q`, and target
margin `4Bp+2 < p`. Half scaling and even moduli make the message-scale mismatch zero.
The actual retained-secret experiment fails with probability at most `4(2t+1)t exp(-t)`,
which is negligible for every message family. The extra factor `t` counts coefficients inside
each noise polynomial; the shared coefficient bound lives in
[Sampling/Concentration.lean](../../CslibFrontier/Crypto/Computational/SIS/ModuleEncryption/Sampling/Concentration.lean).
The [checked clients](../../CslibFrontierTests/Crypto/ModulusSwitchCenteredBinomial.lean)
certify growing native CBD rows and power-of-two uniform matrix-entry samples, with unary
parameters and binary outputs, and check their semantic modular laws. They also prove positive
actual failure at `t=1`: `q=64`, `p=32`, errors all eight and supported secrets produce phase 29
and decode a true message incorrectly. The displayed bound is below one at `t=10`.
This is correctness for explicit laws, not a small-secret security reduction. Deterministic
unswitched native key generation and decryption (`exists_computableInPolyTime_moduleLWEKeyGen`,
`exists_computableInPolyTime_moduleLWEDecrypt`), randomized CBD key generation
(`exists_isPPTOn_moduleLWEKeyGenJoint`), and coefficient conversion in
[`ModulusSwitch/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/ModulusSwitch/Native.lean)
are certified above; native encryption, switched-decryption assembly and seed codecs remain
separate.

Discrete-logarithm and factoring cryptanalysis lives in two algebra-level modules. Import
[`DiscreteLog/PohligHellman.lean`](../../CslibFrontier/Crypto/Computational/DiscreteLog/PohligHellman.lean)
for the Pohlig–Hellman subgroup reduction and CRT uniqueness (`pohligHellman_subgroup_modEq`,
`pohligHellman_crt_modEq`), the prime-power digit step (`pohligHellman_step`), the smooth/rough
trial-division split (`smoothDivisorSeq`, `coprime_smoothDivisorSeq_div`) and composite-order CRT
extraction from two Schnorr transcripts (`extractModRough`, `crtCombine_extractModRough_eq`; the
recombination `crtCombine` itself is in
[`Foundations/Data/Nat/ChineseRemainder.lean`](../../CslibFrontier/Foundations/Data/Nat/ChineseRemainder.lean),
which that module imports publicly). These are correctness identities under explicit positivity,
divisor, inverse and range hypotheses; there is no executable Pohlig–Hellman solver, subgroup
discrete-log solver or running-time bound. Import
[`Factoring/PollardRho.lean`](../../CslibFrontier/Crypto/Computational/Factoring/PollardRho.lean) for
`rhoFactorLoop N F B x y`, a `B`-step Floyd loop over a caller-supplied walk on `(ZMod N)ˣ`. Every
`some d` output is a nontrivial factor (`isNontrivialFactor_of_rhoFactorLoop_eq_some`), `none` is
characterized exactly (`rhoFactorLoop_start_eq_none_iff`), and `floyd_cycle_modEq` turns a
modulo-`p` collision into a tortoise-and-hare meeting modulo `p`. That meeting need not give a
distinct pair modulo `N`; the heuristic success probability and `O(N^{1/4})` running time are not
formalised, and the bounded loop has no native cost certificate. The
[checked examples](../../CslibFrontierTests/Crypto/GroupCryptanalysis.lean) run Katz–Lindell's
Example 10.5 in `(ZMod 31)ˣ`, CRT recombination for `12 = 4 * 3`, and
`rhoFactorLoop 15 walk15 4 1 1 = some 3`.

For composite-modulus number-theoretic hardness assumptions, import [`Factoring.lean`](../../CslibFrontier/Crypto/Computational/Factoring.lean), [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean), [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean), and [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], §§9.2.3–9.2.4, §15.1.1, §§15.4.1–15.4.3, and §§15.5.1–15.5.2; checked examples and reduction clients are in [`CslibFrontierTests/Crypto/QuadraticResiduosity.lean`](../../CslibFrontierTests/Crypto/QuadraticResiduosity.lean), [`CslibFrontierTests/Crypto/RSATrapdoor.lean`](../../CslibFrontierTests/Crypto/RSATrapdoor.lean), and [`CslibFrontierTests/Crypto/RabinFactoring.lean`](../../CslibFrontierTests/Crypto/RabinFactoring.lean)). [`Factoring.lean`](../../CslibFrontier/Crypto/Computational/Factoring.lean) defines the shared challenge encoding `encModulusChallengeInput`, the distribution-indexed integer-factoring experiment `modulusFactoringGame` ([katzlindell20][katzlindell20], Definition 9.45; for context only, [bs23][bs23], §16.4, p. 696, which states no factoring experiment), `ModulusFactoringHard` (`ModulusFactoringHard.congr`), and unique prime-product factorization `mul_eq_mul_primes_cases`. In [`QuadraticResiduosity.lean`](../../CslibFrontier/Crypto/Computational/QuadraticResiduosity.lean) ([katzlindell20][katzlindell20], Section 15.4, Proposition 15.23, and Definition 15.27; for context only, [bs23][bs23], Appendix A.2.3, p. 1097), quadratic residues reuse Mathlib's `IsSquare` and `Subgroup.square` (`Subgroup.mem_square`, `mem_quadResidueSet_iff`), `jacobiSymbol p q` multiplies the Legendre symbols on `(ZMod (p * q))ˣ`, `jacobiPosSet_eq_disjoint_union` and `card_quadResidueSet_eq_card_positiveNonresidues` partition `J_N^{+1}` into equal-sized `quadResidueSet` (`QR_N`) and `positiveNonresidues` (`QNR_N^{+1}`) for distinct odd primes `p ≠ q`, `blumSqrt p q` inverts squaring on `QR_N` for Blum moduli `IsBlumModulus p q` (`blumSqrt_sq`, `sq_bijOn_quadResidueSet`, `neg_one_mem_positiveNonresidues`), `QuadraticResiduosityHard` compares `qrRealGame` against `qrIdealGame`, and `QuadraticResiduosityHard.modulusFactoringHard` reduces integer factoring to quadratic residuosity with exact advantage preservation (`advantage_qrGame_factorToQR`) via `factorToQR` and `qrEulerTest` (testing Euler's criterion `y ^ (a / 2) % a = 1` on a recovered factor `a`). The unit Chinese remainder isomorphism `ZMod.unitsChineseRemainder` and the square facts behind the count (`ZMod.isSquare_iff_unitsChineseRemainder`, `ZMod.two_mul_card_squares_units`) are in [`ZMod/CRTUnits.lean`](../../CslibFrontier/Foundations/Data/ZMod/CRTUnits.lean). In [`RSATrapdoor.lean`](../../CslibFrontier/Crypto/Computational/RSATrapdoor.lean) ([katzlindell20][katzlindell20], Definitions 9.46 and 15.1), `rsaEval N e x = x ^ e % N` and `rsaInvert N d y = y ^ d % N` are certified in polynomial time (`computableInPolyTime_rsaEval`, `computableInPolyTime_rsaInvert`) and proved mutually inverse across all residues `x < N` (`rsaInvert_rsaEval`, `rsaEval_rsaInvert`), inducing bijections both on `Fin N` (`rsaEval_bijective_fin`, including nonunits dividing `p` or `q`) and on `(ZMod N)ˣ` (`rsaEval_bijective_units`), with `rsaInversionGame` running `inversionExperiment` on `x` drawn uniformly from `Fin desc.modulus` (`RSAOneWay`, whereas Definition 9.46 samples uniformly from `(ZMod N)ˣ`). An `RSAInverter` maps the security parameter, a public key `pk : RSAPublicKey` (fields `N`, `e`) and a residue `y : Fin pk.N` to a `ProbComp (Fin pk.N)`; `RSAInverter.IsPPT` asks for one uniform strict PPT machine reading `encRSAInput` (the unary security parameter, the public key `(N, e)` (`N` framed followed by `e`), and `y` in binary, each of the three fields framed except the last) and writing the returned residue in binary. Because RSA evaluation is a bijection on `Fin N`, accepting any preimage is the same as recovering `x` (`rsaInversionGame_eq`), and `rsaOneWay_iff_encoded` shows that `RSAOneWay` is the word-level assumption over inverters that read the same layout on keys with `0 < N` and may output any natural number. In [`RabinFactoring.lean`](../../CslibFrontier/Crypto/Computational/RabinFactoring.lean) ([katzlindell20][katzlindell20], Definition 9.45, §15.3.1, §15.5.1, Lemma 15.35, Theorem 15.36, Proposition 15.37, and Theorem 15.38), `factoringHard_iff_modulusFactoringHard` and `FactoringHard.of_modulusFactoringHard` connect `FactoringHard gen` to `ModulusFactoringHard` on `(gen n).map BlumDesc.modulus` (`QuadraticResiduosityHard.factoringHard`), and `rabinOneWay_iff_factoringHard` establishes `RabinOneWay gen ↔ FactoringHard gen` for Blum moduli via explicit certified PPT reductions `factorToRabin` (computing `crtSqrt y a b` from a nontrivial factorization `a * b = N`, with exact loss `1` in `succProbability_factoringGame_le`) and `rabinToFactor` (`rabinOneWay_of_factoringHard`, `factoringHard_of_rabinOneWay`). Across these modules, generator families (`setup : ℕ → PMF ModulusDesc`, `RSAGen := ℕ → PMF RSADesc`, `BlumGen := ℕ → PMF BlumDesc`) are arbitrary `PMF` families over valid parameter tuples without bundled prime-generation algorithms or bit-length bounds in `n`, and adversaries/reductions use uniform native strict-PPT (`IsPPTOn`) on `(1^n, ...)` with binary `encNat` encodings (charging the full encoded input and sampled/callback output uniformly before `n`). Rather than assuming an exact uniform sampler on `(ZMod N)ˣ`, `rabinInversionGame` and `rabinToFactor` use an original dyadic all-residue sampling variant that draws a uniform `2 * N.bits.length`-bit list `r` (`x = ofBits r < 2^(2 * bits(N))` with `N^2 ≤ 2^(2 * bits(N))`) and squares `x` modulo `N`: `rabinToFactor` checks `1 < gcd(x, N) < N` first and otherwise queries the inverter on `x^2 % N` to return `rabinFactorPair (x + x') N`, yielding the concrete factor-`3` reduction bound `succProbability_rabinInversionGame_le` without modular rejection-sampling error.

For the Miller–Rabin test as a probabilistic program and for random prime and modulus
generation, import [`MillerRabin.lean`](../../CslibFrontier/Crypto/Computational/MillerRabin.lean)
and [`ModulusGeneration.lean`](../../CslibFrontier/Crypto/Computational/ModulusGeneration.lean)
([katzlindell20][katzlindell20], §§9.2.1–9.2.3, Theorems 9.32 and 9.33 and Algorithm 9.34; checked instances
are in [`CslibFrontierTests/Crypto/MillerRabin.lean`](../../CslibFrontierTests/Crypto/MillerRabin.lean)).
`millerRabinTest n t` runs `t` independent rounds (`millerRabinRound`), each of which negates the
coRP verifier `Complexity.MillerRabin.verifier` on `2 |n|` fresh coins. A prime always passes
(`eval_millerRabinTest_of_prime`), any other `n` passes with probability at most `2⁻ᵗ`
(`eval_millerRabinTest_le_of_not_prime`, reusing `ZMod.two_mul_card_isStrongLiar_le`), and the test
is uniform strict PPT on `(n, 1^t)` (`isPPTOn_millerRabinTest`). `randomPrime n` makes up to `3 n²`
attempts, each drawing a uniform `n`-bit candidate with leading bit `1` (`primeCandidate`) and
running `n` rounds of the test, and returns `none` when every attempt fails. A returned number is
not prime with probability at most `3 n² · 2⁻ⁿ` (`toOuterMeasure_randomPrime_not_prime_le`), has
exactly `n` bits (`mem_support_randomPrime`), and all `n`-bit primes are returned with the same
probability (`eval_randomPrime_some_eq`); the generator is uniform strict PPT on `1^n`
(`isPPTOn_randomPrime`). `genModulus n` multiplies two independent outputs into `(N, p, q)`
(`isPPTOn_genModulus`). Its outputs are not certified, so it is not a `PMF ModulusDesc` or
`BalancedModulus.Desc` family. The density of the `n`-bit primes ([katzlindell20][katzlindell20],
Theorem 9.32), proved in
[`PrimeDensity.lean`](../../CslibFrontier/Foundations/NumberTheory/PrimeDensity.lean)
(`Nat.two_pow_sub_one_le_three_mul_card_primes`) by Erdős's central binomial argument
(`Nat.centralBinom_le_pow_card_primes_Ico`, in
[`CentralBinomPrimes.lean`](../../CslibFrontier/Foundations/NumberTheory/CentralBinomPrimes.lean),
which `PrimeWindow.lean` shares), makes a
candidate prime with probability at least `1 / (3 n)` for `n > 1`
(`inv_three_mul_le_toOuterMeasure_primeCandidate_prime`). So for `n > 1` the generator returns
`none` with probability at most `2⁻ⁿ` (`eval_randomPrime_none_le_inv_two_pow`), and `genModulus`
returns an invalid output with probability at most `(6 n² + 2) · 2⁻ⁿ`
(`toOuterMeasure_genModulus_invalid_le_inv_two_pow`, from the bound
`toOuterMeasure_genModulus_invalid_le` in terms of the probability that a candidate is not prime).

For composite residuosity and Paillier encryption, import
[`CompositeResiduosity.lean`](../../CslibFrontier/Crypto/Computational/CompositeResiduosity.lean) and
[`Paillier.lean`](../../CslibFrontier/Crypto/Computational/Paillier.lean), for IND-CPA security
[`Paillier/Security.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean), and for
the scheme at a fixed modulus
[`Paillier/Finite.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean)
([katzlindell20][katzlindell20], Chapter 15, Proposition 15.6, Claims 15.7–15.9, Definition 15.10,
Construction 15.11, Example 15.12, Theorem 15.13, and Definition 15.14; checked instances are in
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean)).
A balanced modulus is a product `N = p * q` of distinct odd primes of the same bit length
(`BalancedModulus.Valid (p, q)`). The Decisional Composite Residuosity assumption
`DCR setup` ([katzlindell20][katzlindell20], Definition 15.10) compares `dcrRealGame` (drawing an
`N`-th residue `r ^ N mod N ^ 2` for a uniform unit `r`) against `dcrRandomGame` (drawing a uniform
unit modulo `N ^ 2`) under `Game.Indistinguishable` against uniform strict-PPT distinguishers
`IsPPTOn encModulusChallengeInput encBool`, and `DCR.modulusFactoringHard` reduces integer factoring
to `DCR` with factor-`2` loss (`succProbability_modulusFactoringGame_le_two_mul_advantage_dcrGame`)
via `factorToDCR` and `dcrTotientTest` (testing `y ^ ((a - 1) * (b - 1)) % (N ^ 2) = 1`, which holds
on all `N`-th residues and on at most `1 / N ≤ 1 / 2` of `(ZMod (N ^ 2))ˣ` by
`Paillier.unitsEquiv`). The parameter `setup : ℕ → PMF Desc`
is arbitrary: prime factor generation is not constructed, and equal factor bit lengths are not
tied to the security parameter `n`.

Paillier public-key encryption operates over binary words with natural-number encodings `encNat`
and `encPair encNat encNat (N, φ(N))`:

- `keyGen gen n` draws a valid description `(p, q) ← gen n` and emits `pk = encNat N` and
  `sk = encPair encNat encNat (N, φ(N))`. Given `IsPPTOn encUnary encDesc gen`, `isPPTOn_keyGen`
  proves that key generation is uniform strict PPT.
- `encrypt n pk m` draws a candidate residue using `ProbComp.sampleModNat (n + |N|) N` and maps
  nonunits to `1` via `unitOrOne N r = if gcd(r, N) = 1 then r else 1`, computing the ciphertext as
  `c = (1 + N) ^ m * r ^ N mod N ^ 2`. `isPPTOn_encrypt` proves encryption is uniform strict PPT.
- `decrypt sk ct` computes `((c ^ φ(N) mod N ^ 2) - 1) / N * φ(N)⁻¹ mod N` using square-and-multiply
  exponentiation and Euler's totient inversion `φ(N) ^ (φ(N) - 1) mod N` (`gcd(N, φ(N)) = 1` by
  `BalancedModulus.Desc.coprime_totient`, Katz–Lindell Claim 15.7), certified polynomial-time by
  `computableInPolyTime_decrypt`.
- `decrypt_encrypt` establishes perfect correctness: for any key pair in the support of `keyGen gen n`
  and message `m < ofBits pk = N`, decrypting any supported ciphertext recovers `encNat m`.
- `addCiphertexts pk ct₁ ct₂` multiplies ciphertexts modulo `N ^ 2`. `decrypt_addCiphertexts`
  proves preservation of plaintext addition under decryption: combining supported encryptions of `m₁`
  and `m₂` yields a ciphertext that decrypts to `(m₁ + m₂) mod N`.

For the word scheme only this decryption-side addition identity is established; the second condition
of Katz–Lindell Definition 15.14—distributional equality between combined ciphertexts and fresh
encryptions of the sum—does not hold for the dyadic sampler with `unitOrOne` (e.g. at `N = 143`,
`n = 0`, and `m₁ = m₂ = 0`, fresh `encNat 1` has mass `44 / 256`, whereas multiplying two independent
encryptions yields mass `2316 / 65536 = 579 / 16384`).

[`Paillier/Finite.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Finite.lean) states the
scheme at one modulus `N` with typed values, as the Diffie–Hellman experiments are stated at one
group. `paillierEncrypt N m` draws `r` uniformly from the units `(ZMod N)ˣ` and returns the unit
`oneAddPowHom N (ofAdd m) * powSelfHom N r` of `ZMod (N ^ 2)`; `paillierDecrypt N t c` is
`logOneAdd N (c ^ t) * t⁻¹`, where `Paillier.logOneAdd` is the function `L` of Construction 15.11.
With `t = φ(N)` and `gcd(N, φ(N)) = 1`, decryption is perfectly correct
(`paillierDecrypt_of_mem_support`) and additive on products (`paillierDecrypt_mul`), and the
second condition of Definition 15.14 holds: multiplying any encryption of `m₁` by a fresh
encryption of `m₂` gives exactly a fresh encryption of `m₁ + m₂` (`eval_mul_paillierEncrypt`,
`eval_paillierEncrypt_mul_paillierEncrypt`). The fixed-modulus DCR worlds `dcrRealExperiment N D`
and `dcrRandomExperiment N D` are in
[`CompositeResiduosity/Finite.lean`](../../CslibFrontier/Crypto/Computational/CompositeResiduosity/Finite.lean),
and the asymptotic games `dcrRealGame` and `dcrRandomGame` are `Game.withSetup` over them.
`paillierCPAExperiment N A b` is the left-or-right experiment `lrExperiment` against a two-stage
adversary `A : TwoStage ℕ (MessagePair (ZMod N)) (ZMod (N ^ 2))ˣ Bool σ` that receives the public
key `N`. `paillierCPAAdvantage_le_dcrAdvantage` bounds its
advantage by `dcrAdvantage N (paillierToDCR N A false) + dcrAdvantage N (paillierToDCR N A true)`,
with no sampling loss. Connecting this bound to `DCR` and to the word scheme is a separate step.

IND-CPA security (Katz–Lindell Theorem 15.13) is in
[`Paillier/Security.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Security.lean).
Challenge pairs are admissible when both messages are below the modulus (`validMessages n pk m₀ m₁`,
i.e. `m₀, m₁ < ofBits pk`). `DCR.indcpaOn_paillier` proves
`Encryption.INDCPAOn validMessages encNat (keyGen gen) encrypt` from `DCR (fun n => eval (gen n))`
and the extra hypothesis `hsize`: every description in the support of `gen n` has primes of at least
`n` bits. The reduction `dcrDistinguisher A b` answers the challenge with `(1 + N) ^ m_b * y mod N ^ 2`
and is uniform strict PPT (`isPPTOn_dcrDistinguisher`). The book samples the encryption randomness
uniformly from the units modulo `N`; here `encrypt` uses the dyadic sampler with `unitOrOne`, which is
within `N / 2 ^ (n + |N|) + (N - φ(N)) / N` of uniform on the units. Under `hsize` this costs at most
`5 / 2 ^ n` per real hop (`Game.advantage_sampleModNat_units_le` in
[`UnitSampling.lean`](../../CslibFrontier/Crypto/Computational/UnitSampling.lean), which also
defines `unitOrOne`; both are shared with Goldwasser–Micali below), so the IND-CPA advantage is at most `10 / 2 ^ n` plus the two DCR
advantages; without a growth condition on the primes the non-unit loss need not be negligible. The
distributional-homomorphism gap above is unaffected.
[`CslibFrontierTests/Crypto/Paillier.lean`](../../CslibFrontierTests/Crypto/Paillier.lean) checks the
concrete parameters of Example 15.12 (`N = 187`, `m = 175`, `r = 83`, `c = 23911`), homomorphic
decryption to `12` and `7` modulo `143`, validity of `(11, 13)`, uniform strict PPT for a constant
generator `constGen`, and end-to-end correctness and homomorphic addition on its supported key pair;
for IND-CPA it evaluates `validMessages` on admissible and inadmissible pairs and applies
`isPPTOn_dcrDistinguisher` and `DCR.indcpaOn_paillier` to a concrete strict-PPT adversary. At
`N = 143` it applies fixed-modulus correctness, additive decryption, the distributional
homomorphism and `paillierCPAAdvantage_le_dcrAdvantage` to a concrete two-stage adversary.

For Goldwasser–Micali public-key encryption under `QuadraticResiduosityHard`, import
[`GoldwasserMicali.lean`](../../CslibFrontier/Crypto/Computational/GoldwasserMicali.lean)
([katzlindell20][katzlindell20], §15.4.4, Definition 15.14, Construction 15.28, Theorem 15.29, and
Exercises 15.11–15.12; checked instances are in
[`CslibFrontierTests/Crypto/GoldwasserMicali.lean`](../../CslibFrontierTests/Crypto/GoldwasserMicali.lean)).
The deterministic certificates compose plain polynomial-time arithmetic, Boolean tests and
encoded equality; the encryption and attack certificates use these directly as strict-PPT callbacks.
`KeyDesc` extends `ModulusDesc` (distinct odd primes `p`, `q`) with a residue `z < p * q`
representing an element of `positiveNonresidues p q` (`KeyDesc.ofBlum` specializes to Blum primes `p % 4 = 3`, `q % 4 = 3` with `z = N - 1`, Exercise
15.12), and `keyGen gen` wraps an abstract generator `gen : ℕ → ProbComp KeyDesc` (prime and
nonresidue sampling are not constructed) emitting `pk = encPair encNat encNat (N, z)` and
`sk = encPair encNat encNat (p, q)` (`isPPTOn_keyGen`). `encrypt` draws randomness via
`ProbComp.sampleModNat (n + |N|) N` with `unitOrOne N` to output `encNat ((z^m * r^2) mod N)`
(`isPPTOn_encrypt`), `decrypt` tests quadratic residuosity modulo `p` and `q` via Euler's criterion
`powMod p c ((p - 1) / 2)` (`computableInPolyTime_decrypt`, `decrypt_encrypt`), and
`mulCiphertexts` multiplies ciphertexts modulo `N` (`computableInPolyTime_mulCiphertexts`,
`decrypt_mulCiphertexts`). As with Paillier, distributional XOR homomorphism and re-randomization
(Definition 15.14, Exercise 15.11) hold on the ideal unit-sampling law `idealEncrypt`
(`idealEncrypt_mulCiphertexts_eq`, `rerandomize_idealEncrypt_eq`), whereas the dyadic `sampleModNat`
with `unitOrOne` approximates uniform `(ZMod N)ˣ` within `5 / 2 ^ n` under `hsize : n ≤ d.p.size ∧
n ≤ d.q.size` (`advantage_encrypt_idealEncrypt_le`). The security headline is the Blum-modulus
variant: `blumKeyGen gen` draws only a modulus `d ← gen n : ProbComp ModulusDesc` and publishes
`blumPublicKey N = ⟨N, N - 1⟩` (`isPPTOn_blumKeyGen`, `decrypt_encrypt_blumKeyGen`), and
`indcpa_blumGoldwasserMicali` proves single-bit `Encryption.INDCPA (blumKeyGen gen) encrypt` from
`QuadraticResiduosityHard` relative to `gen`, Blum moduli and `n`-bit primes on `gen`'s support,
with no premise about the key generator. Its reduction `blumQRDistinguisher` encrypts `m₀` and
multiplies the ciphertext by the challenge `y` when `m₀ ≠ m₁`: a residue leaves an encryption of
`m₀`, and an element of `QNR_N^{+1}`, which is `-1` times a square
(`isSquare_mul_of_mem_positiveNonresidues`), turns it into an encryption of `m₁`. The reduction is
certified strict PPT (`isPPTOn_blumQRDistinguisher`) and the loss is only a `20 / 2 ^ n` sampling
tail (`advantage_blumGame_le_qr`). For the ideal key law `publicKeyLaw setup` (uniform
`z ∈ QNR_N^{+1}`), `advantage_publicKeyGame_le_qr` bounds single-bit advantage by factor-`2` QR
loss plus `10 / 2 ^ n` via `qrDistinguisher`, and `advantage_publicKeyWordGame_le_qr` bounds
bounded-word `encryptWord` advantage with factor-`2` QR loss independent of `maxLen n` plus
`(10 * maxLen n) / 2 ^ n` via lossy quadratic-residue public keys and `qrWordDistinguisher`; the
asymptotic forms are `indistinguishable_publicKeyGame` and `indistinguishable_publicKeyWordGame`.
`publicKeyLaw` is a distribution, not a key generator: no `gen` whose `keyGen gen` matches it is
constructed, so these do not yet give security of `keyGen gen`. Modulus samplers are arbitrary laws
throughout. Conversely, `jacobiAttackAdversary` (`jacobiAttackAdversary_isPPT`) achieves
exact chosen-message advantage `1` whenever `z ∈ jacobiNegSet p q`
(`advantage_jacobiAttackAdversary_eq_one`), witnessing the necessity of `J_N(z) = +1`.

The [Naor–Reingold evaluator](../../CslibFrontier/Crypto/Computational/NaorReingold.lean),
[security reduction](../../CslibFrontier/Crypto/Computational/NaorReingold/Security.lean) and
[uniform PRF construction](../../CslibFrontier/Crypto/Computational/NaorReingold/PRF.lean)
compose plain `ComputableInPolyTime` certificates for word evaluation, tape parsing and captured
query generation. The reduction uses `IsOraclePPTOn.isPPTOn_runState`: certify the prepared input,
initial cache and unary resource allowance, then bound every supported reply and the added encoded
cache storage. The allowance does not replace the invariant on every cached prefix.
The [Naor–Reingold test client](../../CslibFrontierTests/Crypto/NaorReingold.lean) supplies the
public construction and security endpoints.

For two-party key exchange secure against passive eavesdroppers ([katzlindell20][katzlindell20], §11.3, Definition 11.1, Construction 11.2, Theorem 11.3, pp. 390–395, and Exercises 11.3–11.4, pp. 399–400), import [`KeyExchange.lean`](../../CslibFrontier/Crypto/Computational/KeyExchange.lean) and [`Encryption/PublicKeyCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyCPA.lean) (checked in [`CslibFrontierTests/Crypto/KeyExchange.lean`](../../CslibFrontierTests/Crypto/KeyExchange.lean)). `KeyExchange T K` models a protocol by its honest-execution law `execute : ℕ → PMF (Outcome T K)`, with keys in a set `K transcript` named by the transcript (`KeyExchange.Correct`; honest-party efficiency is not bundled). An `Eavesdropper T K` is typed: it receives the security parameter and a `View T K` (a transcript and a candidate key), and its efficiency is `Eavesdropper.IsPPT encT encK`, read through the `enc_structure` encoding `encView`. `realGame` and `idealGame` draw the view `realView` (transcript and Alice's key) or `idealView` (transcript and a fresh ideal key) and run the eavesdropper on it (`EavSecure`, `EavSecureBits`); `withSetup_realView_bind` and `withSetup_idealView_bind` split off a setup draw. Over any `PrimeOrderGroupFamily`, the transcript is the record `DHTranscript` and the key a group element (`DHKey`, `encDHKey`). At a fixed group, `dhExecution` is correct (`dhKeyExchange_correct`) and its real and ideal experiments are the DDH experiments of the typed distinguisher `dhEavToDDH` (`withSetup_realView_dhExecution`, `withSetup_idealView_dhExecution`); `dhKeyExchange setup` draws the group first, which gives `realGame_dhKeyExchange`, `idealGame_dhKeyExchange` and `EavSecure` against the uniform group-element ideal key `dhIdealKey` under `DDH` (`DDH.dhKeyExchange_eavSecure`). The test derives the word-level statement for eavesdroppers on the encoded transcript and key. At a fixed group, the active man-in-the-middle execution `dhMitmExecution` shares keys with both parties while each party's view has the law of `realView` of an honest execution (`dhMitmExecution_keys`, `map_aliceView_dhMitmExecution`, `map_bobView_dhMitmExecution`), and the 3-message XOR protocol `xorKeyExchange`, whose transcript is the record `XorTranscript`, is correct yet broken with advantage at least `1 / 2` by `xorEavesdropper` (`isPPT_xorEavesdropper`, `not_eavSecureBits_xorKeyExchange`). In `Encryption/PublicKeyCPA.lean`, `cpaOracleGameOn`, `WordINDCPAOracleOn`, and `WordINDCPAOracle` equip both stages of a `WordCPAAdversary` with an explicit public-key encryption oracle `encryptionOracle`, and `INDCPAOn.wordINDCPAOracleOn` and `WordINDCPA.wordINDCPAOracle` prove that single-challenge eavesdropping security implies oracle-CPA security whenever `encrypt` is uniform strict PPT ([katzlindell20][katzlindell20], §12.2.1, Proposition 12.3, p. 406; the multi-message left-or-right Theorem 12.6 is not formalized).

For the RSA least-significant-bit experiment and algebraic attacks on plain RSA, import [`RSALeastSignificantBit.lean`](../../CslibFrontier/Crypto/Computational/RSALeastSignificantBit.lean) and [`RSAAttacks.lean`](../../CslibFrontier/Crypto/Computational/RSAAttacks.lean) ([katzlindell20][katzlindell20], §9.2.5, pp. 334–336, §12.5.1, pp. 436–440, and §12.5.3, pp. 443–445; checked instances are in [`CslibFrontierTests/Crypto/RSALeastSignificantBit.lean`](../../CslibFrontierTests/Crypto/RSALeastSignificantBit.lean) and [`CslibFrontierTests/Crypto/RSAAttacks.lean`](../../CslibFrontierTests/Crypto/RSAAttacks.lean)). `rsaLSBGame` samples `desc ← gen n` and a uniform residue `x ← Fin desc.modulus` (matching `rsaInversionGame` rather than `(ZMod N)ˣ`) and asks an `RSAPredictor` (with `RSAPredictor.IsPPT`, reading `encRSAInput` and writing a bit) for `x.testBit 0` given `pk.eval x`. The library does not state the hard-core property of this bit as an assumption, since the literature proves it from the RSA assumption ([#5578](https://github.com/cslib-community/cslib-frontier/issues/5578)). For odd `N`, `two_pow_mul_mod_mod_two` equates the parity of `2 ^ k * x % N` (`k ≠ 0`) with that of `⌊2 ^ k * x / N⌋`, `lsbRecover_lsbQueries` recovers `x` from the parities of the preimages of the `m` doubling queries `2 ^ (k * e) * y % N` once `N ≤ 2 ^ m`, and `lsbInverter` wins `rsaInversionGame` with probability `1` given a predictor that is always correct on the modulus (`eval_lsbInverter`, `succProbability_rsaInversionGame_lsbInverter`). `computableInPolyTime_lsbQueries`, `computableInPolyTime_lsbRecover`, and `isPPT_lsbInverter` certify uniform strict-PPT efficiency for `lsbInverter` whenever the predictor is PPT, yielding `RSAOneWay.not_frequently_alwaysCorrect_lsbPredictor` on eventually odd moduli; the noisy reconstruction of Theorem 12.31 for predictors with small noticeable bias, and with it the hard-core theorem, remains open. `RSAAttacks.lean` proves plain-RSA multiplicative malleability (`rsaEval_mul`, `rsaInvert_rsaEval_mul`), common-modulus recovery of every message `m` coprime to `N` from its encryptions under coprime exponents `e₁`, `e₂` by Shamir's trick (`commonRoot_rsaEval`: `commonRoot N e₂ e₁ (rsaEval N e₁ m) (rsaEval N e₂ m) = m % N`), unreduced short-message and pairwise-coprime CRT broadcast `e`-th root recovery (`rsaEval_eq_pow_of_pow_lt`, `eq_of_pow_eq_rsaEval`, `chineseRemainderOfList_rsaEval_eq_pow`, `eq_of_pow_eq_chineseRemainderOfList_rsaEval`), factoring `N` from `(N, φ(N))` (`factorOfTotient_eq`, `RSADesc.factorOfTotient_eq`, `computableInPolyTime_factorOfTotient`), the polynomial-time equivalence `totientHard_iff_modulusFactoringHard` (`TotientHard.modulusFactoringHard`, `ModulusFactoringHard.totientHard`, after Theorem 9.49) between `TotientHard` (`totientGame`) and `ModulusFactoringHard` via `factorToTotient` and `totientToFactor`, the certified PPT hierarchy `RSAOneWay` $\Rightarrow$ `RSAKeyRecoveryHard` (`rsaKeyRecoveryGame`) $\Rightarrow$ `TotientHard` $\Leftrightarrow$ `ModulusFactoringHard` (`RSAOneWay.rsaKeyRecoveryHard`, `RSAOneWay.totientHard`, `RSAOneWay.modulusFactoringHard`, `RSAKeyRecoveryHard.totientHard`, `RSAKeyRecoveryHard.modulusFactoringHard`) via `totientToKeyRecovery`, `keyRecoveryToRSA`, and `factorToRSA` (using the polynomial-time binary modular inverse `BinaryGcd.modInv`, `BinaryGcd.modInv_eq_zmod_inv_val`, and `ComputableInPolyTime.binary_modInv` in [`PolyTime/Nat/Gcd.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Gcd.lean)), the general nontrivial-square-root factoring lemmas `gcd_sub_one_proper_of_sq_modEq_one` and `gcd_add_one_proper_of_sq_modEq_one` for any `N` and `y`, and the deterministic steps `RSADesc.pow_mul_sub_one_modEq_one`, `RSADesc.gcd_sub_one_proper`, and `RSADesc.gcd_add_one_proper` of Corollary 9.51; the reverse randomized reduction from factoring to `RSAKeyRecoveryHard` (Theorem 9.50 / Corollary 9.51) is not yet formalized.

For RSA with a uniform unit preimage ([bs23][bs23], §10.6.2, Theorem 10.5, p. 416), import
[`RSAUnitInversion.lean`](../../CslibFrontier/Crypto/Computational/RSAUnitInversion.lean).
`rsaUnitInversionGame gen A n`, the book's game for `uRSAadv`, is `rsaInversionGame` with the
preimage `x` drawn uniformly from `(ZMod N)ˣ` instead of `Fin N`; the inverter still receives and
returns residues in `Fin N` (`RSADesc.unitResidue`). `RSAUnitOneWay gen` says that every PPT
inverter wins it with negligible probability. `unitRSAToRSA A`, the book's wrapper `B`, runs `A`
on a challenge `y` coprime to `N` and otherwise returns `rsaNonUnitRoot N e y`, computed from `N`
and `e` alone: `0` for `y = 0`, and otherwise `y ^ d' % N` with `g = gcd(y, N)` and
`d' = BinaryGcd.modInv e ((g - 1) * (N / g - 1))`. For every `desc : RSADesc` with modulus `N`
and exponent `e`, `coprime_rsaEval_iff` says that `rsaEval N e x` is coprime to `N` exactly when
`x` is, and `rsaNonUnitRoot_rsaEval` says that `rsaNonUnitRoot N e (rsaEval N e x) = x` whenever
`x < N` and `x` is not coprime to `N`. `computableInPolyTime_rsaNonUnitRoot` shows that
`rsaNonUnitRoot` is computable in polynomial time whenever `N`, `e` and `y` are, as natural
numbers on `encNat`, and `N` is positive; `isPPT_unitRSAToRSA` shows that `unitRSAToRSA A` is PPT
whenever `A` is. `succProbability_rsaUnitInversionGame_le` is Theorem 10.5: at every security
parameter and for every key law `gen`, the success probability of `A` in `rsaUnitInversionGame`
is at most that of `unitRSAToRSA A` in `rsaInversionGame`. Hence `RSAOneWay gen` implies
`RSAUnitOneWay gen` (`RSAOneWay.rsaUnitOneWay`). The book states the theorem for `ℓ > 2` and odd
`e > 2`, the inputs of its key generator `RSAGen(ℓ, e)`. Here keys come from any law on
`RSADesc` with no hypothesis on it: the proof uses only that `N = p * q` for distinct primes `p`
and `q` and that `e * d ≡ 1` modulo `(p - 1) * (q - 1)`, so `p = 2` and `e = 1` are allowed.
Exercise 10.26 (p. 431), the converse with a loss of `2 ^ -(ℓ - 2)`, is not formalized. The
[checked examples](../../CslibFrontierTests/Crypto/RSAUnitInversion.lean) cover `N = 33`, the
cases `p = 2` and `e = 1`, and an instance showing that the branch for `y = 0` is needed, and
[`AssumptionNonvacuity.lean`](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) shows
that `RSAUnitOneWay` fails for a fixed key (`not_rsaUnitOneWay_const`).

For the RSA hash `H_rsa` ([bs23][bs23], §10.6.2, p. 415, and Theorem 10.7 with the bound (10.3),
pp. 416–417), import [`RSAHash.lean`](../../CslibFrontier/Crypto/Computational/RSAHash.lean). An
`RSAHashKey` is a public key `(N, e)` with a base `y`, encoded by `encRSAHashKey`, and
`rsaHashSetup gen n` draws `desc ← gen n` and a uniform unit `y` modulo `N`. `rsaHash k m` reads
the word `m` as a pair `(a, b)` of binary numbers (`rsaHashDecoder`) and returns
`a ^ e * y ^ b % N`. `validRSAHashInput n k m` holds when `m` is the encoding of that pair, `a < N`,
`a` is coprime to `N` and `b < e`. The hash is an instance of `collisionGameFor`, as `groupHash` in
[`DiscreteLog/GroupHash.lean`](../../CslibFrontier/Crypto/Computational/DiscreteLog/GroupHash.lean)
is. `rsaHashRoot N e y a b a' b'` is Shamir's trick on the pair
ordered by exponent: `commonRoot N e (b' - b) w y` with `w = a * BinaryGcd.modInv a' N % N` when
`b < b'`, and `commonRoot N e (b - b') w y` with `w = a' * BinaryGcd.modInv a N % N` otherwise, so
`commonRoot` keeps natural exponents where the book's proof takes `f = b' - b`. For `0 < N`, a prime
`e`, `y < N`, `Nat.Coprime y N`, `Nat.Coprime a N`, `Nat.Coprime a' N`, `b < e`, `b' < e`,
`b ≠ b'` and `a ^ e * y ^ b ≡ a' ^ e * y ^ b' [MOD N]`, `rsaEval_rsaHashRoot` says that
`rsaEval N e (rsaHashRoot N e y a b a' b') = y`. `rsaHashToRSA A`, the book's adversary `B'`, runs
the collision finder `A` on the key `(N, e, y)` and returns `rsaHashRoot` of the two decoded pairs
without checking that they collide. `isPPT_rsaHashToRSA` shows that `rsaHashToRSA A` is PPT
whenever `A` is PPT on `(1ⁿ, k)`; `computableInPolyTime_rsaHash` and
`computableInPolyTime_validRSAHashInput` show that the hash and its domain are computable in
polynomial time from the encoded key and word. At every security parameter `n` where `e` is prime
for every key in the support of `gen n`,
`succProbability_collisionGameFor_rsaHash_le_rsaUnitInversionGame` bounds the success probability
of `A` in the collision game by that of `rsaHashToRSA A` in `rsaUnitInversionGame`, and
`succProbability_collisionGameFor_rsaHash_le_rsaInversionGame`, the bound (10.3), by that of
`unitRSAToRSA (rsaHashToRSA A)` in `rsaInversionGame`. Hence, if for all sufficiently large `n`
`e` is prime for every key in the support of `gen n`, then `RSAUnitOneWay gen` and `RSAOneWay gen`
each make `rsaHash` collision resistant on `validRSAHashInput` under `rsaHashSetup gen`
(`RSAUnitOneWay.collisionResistantForOn_rsaHash`, `RSAOneWay.collisionResistantForOn_rsaHash`).
The statements differ from the book's in four ways. The bound is `≤` where the book's proof gives
equality, because `rsaHashToRSA` also wins on some words that the game rejects, such as a valid
word followed by `false`. The domain `ℤₙ* × I_e` is the set of words that `validRSAHashInput`
accepts. Digests are natural numbers below `N`, not units modulo `N`. The book fixes a prime `e`,
whereas keys here come from any law on `RSADesc`, with no condition on `ℓ`, and the results assume
that `e` is prime on its support; `e` coprime to `(p - 1) * (q - 1)` is not enough. Exercise 10.26
(p. 431) and the use of `H_rsa` as a compression function in the Merkle–Damgård construction
(p. 416) are not formalized. The accumulator of §10.9 is in `GUOAccumulator.lean` (below), without
its security theorem. The
[checked examples](../../CslibFrontierTests/Crypto/RSAHash.lean) cover a collision at `N = 15`,
`e = 3` and `y = 2` with its root `8`, a word that decodes to a valid pair but is not valid, and, at
`e = 9`, which is coprime to `(3 - 1) * (5 - 1) = 8`, a collision that gives no ninth root of `2`.

For the strong RSA assumption ([bs23][bs23], §10.9, pp. 420–421), import
[`StrongRSA.lean`](../../CslibFrontier/Crypto/Computational/StrongRSA.lean). `GUOParams` holds the
public parameters `(N, g)` of the group `(ZMod N)ˣ`, encoded by `encGUOParams`. In
`strongRSAGame setup A n` the adversary receives `(N, g)` drawn from `setup n` and wins with a pair
`(x, e)` when `isStrongRSASolution (N, g) (x, e)`: `x ^ e` and `g` agree modulo `N`, and `e ≠ 1`
(`isStrongRSASolution_eq_true_iff` for `0 < N`). `StrongRSA setup` says that every PPT adversary
(`StrongRSAAdversary.IsPPT`) wins with negligible probability; the
[assumptions inventory](assumptions.md) lists it as standard. `rsaGUOSetup gen` is the book's
`GGen`: an RSA modulus from the key law `gen` and a uniform unit `g`; every `(N, g)` it draws has
`g` coprime to `N` (`exists_of_mem_support_rsaGUOSetup`). The statement differs from the book's in
two ways. The setup is any law on `GUOParams`, which need not be efficiently samplable or give a
unit `g`, in place of a group of unknown order from an efficient `GGen`; class groups (p. 423) are
not covered. The adversary outputs natural numbers `x` and `e ≠ 1` in place of `x ∈ G` and an
integer `e ≠ ±1`. For a unit `g`, every winning output gives one for the book's game, so for a
setup that gives a unit `g` the book's assumption implies `StrongRSA`; that implication is not
formalized. The book's remark that strong RSA is a stronger assumption than standard RSA (p. 420)
is not formalized either: no implication between `StrongRSA (rsaGUOSetup gen)` and `RSAOneWay gen`
or `RSAUnitOneWay gen` is proved. `not_strongRSA_of_orderMultiple` is the observation of p. 421
that the assumption is false when a multiple `u` of the order of `g` is known. If a
polynomial-time function `u` of the security parameter and `(N, g)` gives `0 < u` and
`g ^ u ≡ 1 [MOD N]` on the support of every `setup n`, then `orderMultipleAdversary u` wins with
probability `1` (`strongRSAGame_orderMultipleAdversary`), and `isPPT_orderMultipleAdversary` shows
that it is PPT. It is `knownOrderAdversary u v` with `v = u + 1`, which outputs
`(knownOrderRoot N u v g, v)`, where `knownOrderRoot N u v g` is `g ^ (v⁻¹ mod u)` modulo `N`.
`powMod_knownOrderRoot` says that this is a `v`-th root of `g` modulo `N` when `0 < u`,
`g ^ u ≡ 1 [MOD N]` and `v` is coprime to `u`, for every `N`. The general form
`not_strongRSA_of_knownOrder` takes any polynomial-time `v ≠ 1` coprime to `u`
(`strongRSAGame_knownOrderAdversary`, `isPPT_knownOrderAdversary`); the book takes `v > 1`. The
[checked examples](../../CslibFrontierTests/Crypto/StrongRSA.lean) cover `N = 15` and `g = 2`,
where `orderMultipleAdversary` with `u = 4` wins, instances showing that `0 < u` is needed in
`powMod_knownOrderRoot` and in `not_strongRSA_of_orderMultiple`, and the failure of the assumption
for `rsaGUOSetup` with a fixed key (`not_strongRSA_rsaGUOSetup_const`).
[`AssumptionNonvacuity.lean`](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) shows
that `StrongRSA` fails for a fixed modulus and unit base (`not_strongRSA_const`), and the checked
examples show that the unit condition is needed there (`strongRSA_const_four_two`).

For Shamir's trick ([bs23][bs23], §10.6.2, Theorem 10.6, p. 416), import
[`RSACommonRoot.lean`](../../CslibFrontier/Crypto/Computational/RSACommonRoot.lean); the group
identity behind it is in
[`Foundations/Algebra/Group/ZPowCoprime.lean`](../../CslibFrontier/Foundations/Algebra/Group/ZPowCoprime.lean).
In any group, if `a` and `b` commute, `a ^ m = b ^ n` and `m * s + n * t = 1` for integers, then
`b ^ s * a ^ t` is an `m`-th root of `b` and an `n`-th root of `a`
(`Commute.zpow_mul_zpow_zpow_eq_right`, `Commute.zpow_mul_zpow_zpow_eq_left`). By
`eq_zpow_mul_zpow_of_zpow_eq`, still with `m * s + n * t = 1`, any `c` with `c ^ m = b` and
`c ^ n = a` equals `b ^ s * a ^ t`, even when `a` and `b` do not commute. For commuting `a` and
`b` and `IsCoprime m n`, `a ^ m = b ^ n` holds exactly when `a = c ^ n` and `b = c ^ m` for some `c`
(`Commute.zpow_eq_zpow_iff_of_isCoprime`; `zpow_eq_zpow_iff_of_isCoprime` is the form for
commutative groups). No group order is assumed. `commonRoot n e f w y` is the book's algorithm on
natural numbers: it returns `y ^ s * (w⁻¹) ^ t mod n` with `s = BinaryGcd.modInv e f`,
`t = (e * s - 1) / f` and `w⁻¹ = BinaryGcd.modInv w n`, and it returns `y mod n` for `f = 0` and
`w mod n` for `f = 1`. For `0 < n`, `Nat.Coprime e f`, `Nat.Coprime w n` and
`w ^ e ≡ y ^ f [MOD n]`, its output `x` satisfies `x ^ e ≡ y [MOD n]`
(`commonRoot_pow_modEq_right`) and `x ^ f ≡ w [MOD n]` (`commonRoot_pow_modEq_left`); under these
hypotheses together with `Nat.Coprime y n`, `x` is coprime to `n`, the book's `x ∈ ℤₙ*`
(`commonRoot_coprime`, which uses `Nat.Coprime y n` only when `f = 0`); for `0 < n` it is below
`n` (`commonRoot_lt`). `computableInPolyTime_commonRoot` shows that it is computable in polynomial
time whenever `n`, `e`, `f`, `w` and `y` are, as natural numbers on `encNat`, with no condition on
their values. The statement differs from the book's in three ways. The exponents are natural
numbers, whereas the book allows negative ones and applies the theorem with `f = b' - b`
([bs23][bs23], proof of Theorem 10.7, p. 417); `rsaHashRoot` orders the pair so that natural
exponents suffice there. The book states only `x ^ e ≡ y`; the second
congruence is the one §10.9 uses to recover each proof from an aggregate ([bs23][bs23], §10.9,
p. 422). The book takes units `w` and `y` modulo `n`, whereas here `w` and `y` are natural numbers,
not necessarily below `n`, and the two congruences assume only `Nat.Coprime w n`: for `f ≠ 0` it
makes `y` coprime to `n`, and for `f = 0` they do not need it. The accumulator of §10.9 is in
`GUOAccumulator.lean` (below), without its security theorem. In `RSAAttacks.lean`,
`commonRoot_rsaEval` applies the
algorithm to the common-modulus attack on plain RSA: for `Nat.Coprime e₁ e₂` and
`Nat.Coprime m N`, `commonRoot N e₂ e₁ (rsaEval N e₁ m) (rsaEval N e₂ m) = m % N`, so
`computableInPolyTime_commonRoot` is also the attack's certificate. The checked examples for the
[identity](../../CslibFrontierTests/Foundations/Algebra/ZPowCoprime.lean) and the
[algorithm](../../CslibFrontierTests/Crypto/RSACommonRoot.lean) include the book's warm-up
`e = 3`, `f = 2`, the case `f = 1`, and instances showing that coprime exponents, a unit `w` and
commutativity are needed.

For the accumulator in a group of unknown order ([bs23][bs23], §10.9, pp. 421–423), import
[`GUOAccumulator.lean`](../../CslibFrontier/Crypto/Computational/GUOAccumulator.lean). The group
is `(ℤ/Nℤ)ˣ` with a base `g`, its elements are natural numbers, and the hash is any `H : X → ℕ`.
`guoCommit N g H S` is `g ^ guoExponent H S mod N`, with the product of the hashes of the finite
set `S` in the exponent, and `guoCommit_insert` raises it to the power `H x` when `x ∉ S` is added.
`guoSubsetWitness N g H S T` is `g` to the product of the hashes over `S \ T`: the membership proof
for `T = {x}`, the book's `π_xy` for `T = {x, y}` and `π_T` in general. Bob's check `b ^ e = c` is
`guoVerifySubset N c e b`. Against `c = guoCommit N g H S`, the witness for `T` passes it with
`e = guoExponent H T` when `T ⊆ S` (`guoVerifySubset_subsetWitness`), the witness for `{x}` with
`e = H x` when `x ∈ S` (`guoVerifySubset_singleton`), and the witness for `{x, y}` with
`e = H x * H y` when `x` and `y` are distinct elements of `S` (`guoVerifySubset_pair`). If `b`
passes with `e * f`, then `b ^ f mod N` passes with `e` (`guoVerifySubset_split`); if `b₁` and `b₂`
pass against a unit `c` with coprime exponents `e` and `f`, Shamir's trick gives a proof that
passes with `e * f` (`guoVerifySubset_commonRoot`). A non-membership proof is a pair `(b, γ)` with
`γ : ℤ`, and `guoVerifyNonMem N g c h b γ` checks that `c` is a unit and that `b ^ h * c ^ γ = g`,
comparing `b ^ h` with `g * c ^ |γ|` when `γ < 0`, so no inverse is computed. Alice's proof
`(guoNonMemWitness N g h E, -guoNonMemCoeff h E)` passes against `c = powMod N g E` whenever `g`
is a unit, `0 < h` and `Nat.Coprime h E` (`guoVerifyNonMem_witness`), so it passes against
`guoCommit` for a prime `H x` distinct from the prime hashes of `S` (`coprime_guoExponent`,
`guoVerifyNonMem_guoCommit`). The book's remark that correctness relies on the collision
resistance of `H` is stated as an explicit collision: if `x ∉ S`, `H x` and the hashes of `S` are
prime and `H x` is not coprime to `guoExponent H S`, then some `y ∈ S` other than `x` has
`H y = H x` (`exists_collision_of_not_coprime_guoExponent`); no game against a hash family is
stated. If `a` passes `guoVerifySubset N c h a` and `(b, γ)` passes `guoVerifyNonMem N g c h b γ`
for the same `c` and `h`, then `guoForgeryRoot N a b γ`, which computes `b * a ^ γ mod N`, is an
`h`-th root of `g` modulo `N` (`powMod_guoForgeryRoot`), with no hypothesis on `N`, `g` or `h`:
this is the algebra of the book's security argument (p. 422). Both checks, Alice's non-membership
proof and the root are computable in polynomial time, with `γ` on `encIntBin` and the natural
numbers on `encNat` (`computableInPolyTime_guoVerifySubset`,
`computableInPolyTime_guoVerifyNonMem`, `computableInPolyTime_neg_guoNonMemCoeff`,
`computableInPolyTime_guoNonMemWitness`, `computableInPolyTime_guoForgeryRoot`);
`computableInPolyTime_guoNonMemCoeff` certifies the natural number `-γ` on `encNat`. The
statements differ from the book's in two further places: the book's
`π_T = g ^ (E / ∏ x ∈ T, H x)` equals `guoSubsetWitness` when `T ⊆ S` and no hash is `0`, and for
`0 < H x` Alice's `γ` satisfies `|γ| < H x` where the book has `|γ| ≤ H(x)` (`guoNonMemCoeff_lt`).
Security under strong RSA, a certificate for computing `E` from a list of elements, aggregated
non-membership proofs and class groups are not formalized in this module. The
[checked examples](../../CslibFrontierTests/Crypto/GUOAccumulator.lean) work modulo `35` with
`g = 2` and the hashes `3`, `5` and `7`, and include instances showing that the unit commitment,
the unit base, `0 < h`, prime hashes and the unit check on `c` are needed.

For weak RSA moduli ([bs23][bs23], §16.4.2, pp. 698–699), import
[`Factoring/WeakModuli.lean`](../../CslibFrontier/Crypto/Computational/Factoring/WeakModuli.lean).
Moduli sharing a prime are factored by their gcd (`gcd_mul_mul_of_prime_ne`,
`RSADesc.gcd_modulus_eq_of_p_eq`), which `ComputableInPolyTime.binary_gcd` computes in polynomial
time. Lemma 16.4 is proved over `ℝ` as printed, with the absolute value in the conclusion
`|(p + q) / 2 - √(p * q)| < 1 / 2` (`abs_add_div_two_sub_sqrt_mul_lt_half`), and
`abs_sub_lt_two_mul_rpow_iff` turns its closeness bound `|p - q| < 2 * (p * q) ^ (1 / 4)` into
`(p - q) ^ 4 < 16 * (p * q)`, which `norm_num` decides on numbers. `fermatFactor n` applies
`factorOfTotient` to `n + 1 - 2 * ⌈√n⌉`, with `⌈√n⌉` written as the function that
`binary_ceilSqrt` certifies. The book does not name this algorithm: `fermatFactor` is the
library's name, and it is a single step of Fermat's method, trying only `A = ⌈√n⌉`. It is a
polynomial-time function on binary naturals (`computableInPolyTime_fermatFactor`).
`fermatFactor_mul_eq` shows that it returns `(p, q)` for `q ≤ p` with `p + q` even under the
closeness bound, which also forces `p` and `q` to be positive; primality is not needed. For an RSA
modulus with odd primes, `RSADesc.fermatFactor_eq` shows that it returns `(max p q, min p q)`.
So moduli with close factors are factored in polynomial time; the theorems say nothing about
other moduli. The [checked examples](../../CslibFrontierTests/Crypto/WeakModuli.lean) factor
`10403 = 101 * 103` and two moduli sharing `101`, and show that `fermatFactor` does not factor
`3 * 101` or `3 * 2`.

For RSA-CRT inversion and the gcd identity behind its fault attack ([bs23][bs23], §16.4.3, pp. 701–702), import [`RSACRT.lean`](../../CslibFrontier/Crypto/Computational/RSACRT.lean) (checked instances are in [`CslibFrontierTests/Crypto/RSACRT.lean`](../../CslibFrontierTests/Crypto/RSACRT.lean)). `RSACRTKey` is the key `(p, q, d_p, d_q, q_inv)`, `RSADesc.crtKeyWith desc qInv` derives it from an `RSADesc` with `d_p = d % (p - 1)` and `d_q = d % (q - 1)`, and `RSADesc.crtKey` uses `q_inv = RSADesc.crtQInv`, computed by the extended Euclidean algorithm `BinaryGcd.modInv q p` of [`PolyTime/Nat/Gcd.lean`](../../CslibFrontier/Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Gcd.lean); `RSADesc.crtQInv_eq_zmod_inv_val` proves that it is the representative `((q : ZMod p)⁻¹).val` of the inverse of `q` in `ZMod p`, and `RSADesc.crtQInv_mul_modEq_one` that `crtQInv * q ≡ 1 [MOD p]`. Recombination `RSACRTKey.combine` is `crtCombine` from [`Foundations/Data/Nat/ChineseRemainder.lean`](../../CslibFrontier/Foundations/Data/Nat/ChineseRemainder.lean). For odd `p` and `q` and any `q_inv` with `q_inv * q ≡ 1 [MOD p]`, `RSADesc.invert_crtKeyWith` proves that RSA-CRT inversion equals `rsaInvert n d` on every input; the tests show that it fails for `p = 2`. `RSADesc.gcd_val_pow_sub_combine_eq_q` states the gcd identity behind the fault attack: for any such `q_inv`, that is, any `q_inv` with `q_inv * q ≡ 1 [MOD p]` (oddness is not needed), recombining an `x_q` that is correct modulo `q` with an `x_p` that is wrong modulo `p` gives an output `σ` with `gcd(σ ^ e − h, n) = q`, where `σ ^ e − h` is computed in `ZMod n` and read in `[0, n)`, for any natural number `h` in place of the hash value. The polynomial-time certificates take component functions `α → ℕ`, each computable in polynomial time to `encNat`, as `computableInPolyTime_rsaInvert` does: `computableInPolyTime_crtInvert` certifies RSA-CRT inversion from the key components and the input when `p` and `q` are positive, `computableInPolyTime_crtKeyWith_invert` does the same for `RSADesc.crtKeyWith desc qInv` from `p`, `q`, `d`, `q_inv` and the input, and `computableInPolyTime_gcd_val_pow_sub` certifies the attack's gcd step `gcd(σ ^ e − h, n)` when `n` is positive. In `computableInPolyTime_crtInvert` and `computableInPolyTime_crtKeyWith_invert`, `q_inv` is an input, as in the book's precomputed key. `computableInPolyTime_crtQInv` certifies `RSADesc.crtQInv` from `p` and `q` with no further hypothesis, and `computableInPolyTime_crtKey_invert` certifies RSA-CRT inversion with `RSADesc.crtKey` from `p`, `q`, `d` and the input, with no positivity hypothesis because `p` and `q` are prime. Nothing is proved about an attacker as an adversary in a game, or about signing. The four-times speed-up and FDH-RSA signing are not formalized.

### Elliptic curves over finite fields and Hasse's bound

Import [`EllipticCurve/Hasse.lean`](../../CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/Hasse.lean)
(`CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Hasse`). This is mathematics with no
machine model, group-law algorithm or running time. A curve is Mathlib's `WeierstrassCurve F`, and
its points are the type `W.toAffine.Point`: the point at infinity together with the nonsingular
affine solutions of the Weierstrass equation. The number of points is
`Nat.card W.toAffine.Point`, which is finite over a finite field. The instance `[W.IsElliptic]`
says that the discriminant `W.Δ` is a unit. For a concrete curve over `ZMod p`, prove `W.Δ ≠ 0`
by `decide` and build the instance as `⟨isUnit_iff_ne_zero.2 h⟩`.

- **Odd characteristic.** For a finite field `F` with `ringChar F ≠ 2` and `q = Fintype.card F`,
  `WeierstrassCurve.natCard_point_eq` gives `#E(F) = q + 1 + S`, where `S` is the character sum
  `WeierstrassCurve.cubicCharSum` of the cubic obtained by completing the square.
  `WeierstrassCurve.hasse_bound` gives `(#E(F) - (q + 1))² ≤ 4 q` in `ℤ`, and
  `WeierstrassCurve.abs_natCard_point_sub_le` gives the real form `|#E(F) - (q + 1)| ≤ 2 √q`. The
  proof adapts Manin's elementary argument [manin56][manin56]; the implementation notes of
  [`ManinHeight.lean`](../../CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/ManinHeight.lean)
  say how the Lean steps correspond to his paper.
- **Prime fields `ZMod p`, including `p = 2`.** Completing the square needs `2 ≠ 0`, so the
  general theorem excludes characteristic two. `WeierstrassCurve.hasse_bound_zmod` states
  `p + 1 - 2 √p ≤ #E ≤ p + 1 + 2 √p` for every prime `p` (Theorem 9.72 of
  [katzlindell20][katzlindell20]); for `p = 2` it uses the direct count
  `WeierstrassCurve.natCard_point_zmod_two` (`1 ≤ #E ≤ 5`). Other fields of characteristic two are
  not covered.

The [checked client](../../CslibFrontierTests/Foundations/AlgebraicGeometry/EllipticCurveHasse.lean)
counts the points of `y² = x³ + 3x + 3` over `ZMod 7` (Example 9.69 of
[katzlindell20][katzlindell20]), of `y² + y = x³` over `ZMod 2`, and of two curves over `ZMod 5`
that attain both ends of the bound, and applies each form of the theorem to them. Build it with
`lake build CslibFrontierTests.Foundations.AlgebraicGeometry.EllipticCurveHasse`.

### Lagrange interpolation in the exponent

Boneh–Shoup Lemma 22.1 and Corollary 22.2 ([bs23][bs23], Section 22.1.1, pp. 928–929) say that
the value at any point of a polynomial of degree less than `t` over `Z_q` is a fixed combination of
its values at `t` distinct nodes, with efficiently computable coefficients, and that in a group of
prime order `q` the same combination works in the exponent. Over an arbitrary field, without cost
statements, `Lagrange.eval_eq_sum_eval_basis_mul_eval` and
`Lagrange.eval_smul_eq_sum_eval_basis_smul` in
[`Polynomial/LagrangeEval.lean`](../../CslibFrontier/Foundations/Data/Polynomial/LagrangeEval.lean)
state the identities. Each takes `[Field F] [DecidableEq ι]`, nodes `v` with
`hv : Set.InjOn v s` and a polynomial with `hf : f.degree < #s`; the module form also takes
`[AddCommMonoid M] [Module F M]`. `Lagrange.eval_basis` gives the product formula of the weights,
with no hypothesis.

Import
[`DiscreteLog/Interpolation.lean`](../../CslibFrontier/Crypto/Computational/DiscreteLog/Interpolation.lean)
for the polynomial-time forms. The nodes are a list `nodes : List ℕ` and the point is any `x : ℕ`.

- `lagrangeWeightNat q nodes j x` computes the coefficient of `j` modulo `q` on natural numbers.
  For `[Fact q.Prime]`, `lagrangeWeightNat_cast_eq_eval_basis` takes nodes distinct modulo `q`
  (`hnodes : (nodes.map (Nat.cast : ℕ → ZMod q)).Nodup`) and `hj : j ∈ nodes`, and identifies the
  coefficient with the value at `x` of the Lagrange basis polynomial of `j`. With the same `hnodes`
  and a polynomial `f` over `ZMod q` with `hf : f.degree < nodes.length`,
  `eval_eq_sum_lagrangeWeightNat_mul_eval` is Lemma 22.1 with these coefficients.
  `computableInPolyTime_lagrangeWeightNat` (`@[fun_prop]`) computes the coefficient in polynomial
  time when `q` is the order `F.order d` of a group of a `PrimeOrderGroupFamily` `F`, from a
  description, nodes, node and point computed in polynomial time; it takes no hypothesis on the
  nodes.
- `lagrangeCombine d x shares` combines the group elements of the pairs `(j, h_j)` with those
  coefficients. `lagrangeCombine_eval_smul` is Corollary 22.2 written additively: for a group
  description `d`, nodes distinct modulo `F.order d`, a polynomial `f` with `hf` as above and
  `h : F.Carrier d`, combining the elements `f(j) • h` gives `f(x) • h`.
  `computableInPolyTime_encode_lagrangeCombine` computes the encoding of the combination in
  polynomial time from the description, the point and the list of pairs `(j, F.encode d h_j)`, all
  computed in polynomial time. Its input is the encodings of group elements, not arbitrary words.
  It is not `@[fun_prop]`: when the shares are themselves a `List.map`, fuse the two maps in its
  hypothesis `hshares` with `List.map_map` before calling `fun_prop`, as the client does.

The [interpolation client](../../CslibFrontierTests/Crypto/DiscreteLogInterpolation.lean) computes
coefficients modulo `7`, shows that both hypotheses of `lagrangeWeightNat_cast_eq_eval_basis` are
needed, recovers a constant term in the exponent in every group of every family and applies both
certificates. Check it and the field-level
[Lagrange client](../../CslibFrontierTests/Foundations/Data/Polynomial/LagrangeEval.lean) with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.DiscreteLogInterpolation \
  CslibFrontierTests.Foundations.Data.Polynomial.LagrangeEval
```

### Faithful block-matrix embeddings

Import [`Matrix/BlockEmbedding.lean`](../../CslibFrontier/Foundations/LinearAlgebra/Matrix/BlockEmbedding.lean)
to extend a ring representation `R →+* Matrix κ κ S` entrywise to a ring homomorphism from square
matrices over `R` to flattened block matrices over `S`. `Matrix.blockEmbedding_apply` exposes the
block entries, while `Matrix.blockEmbedding_injective` says that a faithful entry representation
remains faithful after flattening. The rational-circuit rank and deformation developments use this
shared definition instead of owning a specialized copy.

For [QR-UOV Round 3](https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/qruov_specifications.pdf),
Mathlib's `Algebra.leftMulMatrix b` is the injective regular representation `g ↦ Φ_f^g` of
Equation (4) and Lemma 1 (§3.2, p. 13), and `Matrix.blockEmbedding` is the entrywise lift `ϕ`
from §4.1, p. 17. The
[ordinary-module client](../../CslibFrontierTests/Foundations/LinearAlgebra/Matrix/BlockEmbedding.lean)
checks their composition without defining a parallel quotient-ring representation. This API does
not construct the symmetrizer `W`, the structured MQ map, the pull-back bijection, signing or
verification, rank-failure estimates, or the QROM reduction; those remain obligations of the
[post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

### UOV concrete binary fields and encodings

Import [`UOV/Field.lean`](../../CslibFrontier/Crypto/Protocols/UOV/Field.lean) for the exact fields
and individual-element encodings fixed by [UOV v3.0][uov26] §3.3, p. 19. `UOV.F16` and
`UOV.F256` reuse `BinaryField 4` and `BinaryField 8`; `UOV.f16_modulus` and `UOV.f256_modulus`
identify their least-code irreducible polynomials as `X^4 + X + 1` and
`X^8 + X^4 + X^3 + X + 1`. `UOV.f16EquivNibble` and `UOV.f256EquivByte` compose the existing
power-basis coordinates with little-endian `BitString.equivFin`, while `UOV.f16PairEquivByte`
packs the first of two `F16` elements into the low nibble (`low + 16 * high`).

The [client module](../../CslibFrontierTests/Crypto/UOVField.lean) covers nontrivial round trips,
the convention-sensitive generator value `X ↦ 2`, the quotient evaluations `X^4 ↦ 0x03` and
`X^8 ↦ 0x1b`, and low-first packing `(X, 1) ↦ 0x12`. This module does not serialize vectors or
matrices and does not construct UOV keys, signing, verification, retries, assumptions, or a
security reduction; those remain obligations of
[#5219](https://github.com/cslib-community/cslib-frontier/issues/5219) and the
[post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

### Canonical upper-triangular quadratic representatives

Import [`Matrix/UpperTriangularQuadratic.lean`](../../CslibFrontier/Foundations/LinearAlgebra/Matrix/UpperTriangularQuadratic.lean)
(`CslibFrontier.Foundations.LinearAlgebra.Matrix.UpperTriangularQuadratic`) for the canonical
upper-triangular representative `Matrix.upperQuadratic M` of a square matrix `M` over a commutative
ring with a linearly ordered index type (`M.upperQuadratic i i = M i i`,
`M.upperQuadratic i j = M i j + M j i` for `i < j`, and `0` for `j < i`).
`Matrix.isUpperTriangular_upperQuadratic` proves `Matrix.IsUpperTriangular`,
`Matrix.isAlt_toLinearMap₂'_upperQuadratic_sub` proves that `M.upperQuadratic - M` induces an
alternating bilinear form (`LinearMap.IsAlt`), and `Matrix.toQuadraticForm'_upperQuadratic` derives
`M.upperQuadratic.toQuadraticForm' = M.toQuadraticForm'` in every characteristic through Mathlib's
`LinearMap.BilinMap.toQuadraticMap_eq_zero` ↔ `LinearMap.IsAlt` equivalence.
`Matrix.eq_upperQuadratic_of_isUpperTriangular_of_isAlt` and
`Matrix.eq_upperQuadratic_of_isUpperTriangular_of_toQuadraticForm'_eq` prove uniqueness among
upper-triangular matrices.

For [UOV v3.0][uov26] (§3.1, pp. 11–13), `Matrix.upperQuadratic` formalizes the specification's
generic `Upper(M)` representative. The
[ordinary-module client](../../CslibFrontierTests/Foundations/LinearAlgebra/Matrix/UpperTriangularQuadratic.lean)
checks `ZMod 2` (characteristic two) and `ℤ` nonsymmetric matrices and verifies that dropping either
the transpose contribution or lower-triangular zeroing violates uniqueness or quadratic-form
equality. This generic matrix layer does not construct UOV block keys, oil subspaces, signing or
verification algorithms, restart bounds, or ROM/QROM security reductions; those remain obligations
of [#5219](https://github.com/cslib-community/cslib-frontier/issues/5219) and the
[post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

### The `B_{p,∞}` quaternion presentation used by SQIsign

Import [`Quaternion/BpInfinity.lean`](../../CslibFrontier/Foundations/Algebra/Quaternion/BpInfinity.lean)
(`CslibFrontier.Foundations.Algebra.Quaternion.BpInfinity`) for the rational quaternion algebra
used by SQIsign v3.0. Its source identification applies to the scheme prime
`p = c · 2^f - 1`, where `f > 1` and `c` is odd, hence `p ≡ 3 (mod 4)`; the reusable Lean type
itself accepts any rational parameter. `Cslib.BpInfinity p` specializes Mathlib's
`QuaternionAlgebra` to the presentation `i² = -1`, `j² = -p`, and `ij = k = -ji`; the declarations
`BpInfinity.i`, `BpInfinity.j`, and `BpInfinity.k` name these generators, and `i_eq_mk`, `j_eq_mk`,
and `k_eq_mk` connect them to Mathlib's ordinary quaternion coordinates. `BpInfinity.star_mk`
gives coordinate conjugation, while `BpInfinity.reducedNorm_mk` and `BpInfinity.reducedTrace_mk` give
`x² + y² + p(z² + t²)` and `2x`. `BpInfinity.reducedNorm_pos` proves positive definiteness for
`p > 0`.

This is only the exact algebra presentation from SQIsign v3.0, Facts 12–13, Section 2.2.1, and
Algorithms 4.38–4.40. The name records the specification's `B_{p,∞}`; the module does not prove
ramification at `p` and infinity. It also does not supply the maximal order `O₀`, quaternion
lattices or ideals, norm-equation algorithms, the Deuring correspondence, isogenies, SQIsign
algorithms, or any ROM/QROM security statement. The
[checked client](../../CslibFrontierTests/Foundations/Algebra/QuaternionBpInfinity.lean) evaluates
the combined generator expression `1 + 2i + 3j + 4k` at `p = 3` through the ordinary import and
also checks the corresponding explicit-coordinate norm. Positivity and the defining generator
relations are exercised there as well.

### HQC fixed-weight support sampling

Import [`HQC/SupportSampling.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportSampling.lean)
for the `SampleSupport2` program from the [HQC v5.1 specification](https://pqc-hqc.org/doc/hqc_specifications_v5.1.pdf),
p. 19. `sampleSupport2 width n count` draws every word from exactly `width` independent fair bits,
forms candidate `i + floor(word * (n-i) / 2^width)`, and then resolves collisions in descending
index order. `scanSupport` retains the ordered output array; `toFinset_scanSupport` proves that
the literal inner scan gives the same support as the membership-based resolver. For `count ≤ n`,
every output has exactly `count` positions in `range n`. `eval_idealSupport` proves exact
uniformity when each shrinking interval is sampled uniformly instead.

[`HQC/SupportDensity.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportDensity.lean) proves
Proposition 6.2.1's two product bounds for the actual multiply-high choices. The remainder
formulas in Equation (16) are identified by `supportLowerDensity_toReal` and
`supportUpperDensity_toReal`. Use `sampleSupport2_event_bounds` for a Boolean event and
`sampleSupport2_payoff_bounds` for a real payoff nonnegative on valid supports. Nonnegativity
is essential: the source's Lemma 6.5 omits it, and a constant payoff of `-1` refutes that wording.
[Checked examples](../../CslibFrontierTests/Crypto/HQCSupportSampling.lean) include zero/full weight,
collision replacement, and `n=5`, `count=2`, `width=3`, where `{2,4}` has actual probability
`1/16` and ideal probability `1/10`. They also distinguish multiply-high from modulo reduction.

For the finite statistical comparison, import
[`HQC/SupportProbability.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportProbability.lean);
for the native circuit, import
[`HQC/SupportCircuit/Sampler.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportCircuit/Sampler.lean).
Under `count ≤ n` and `n < 2 ^ bits`, the circuit's measured law is exactly `sampleSupport2`
mapped through `BitString.indicatorVector`, every output has weight `count`, and
`supportSamplerDist_closeTo_ideal` bounds its finite discrepancy by
`1 - (supportLowerDensity width n 0 count).toReal`. This is not exact ideal uniformity.
`negligible_one_sub_supportLowerDensity` makes the error negligible only along schedules whose
word width grows sufficiently; it gives no negligibility claim for a fixed width such as `32`.

The construction uses the shared reversible sampler in
[`Quantum/Reversible/Sampling.lean`](../../CslibFrontier/Computability/Circuit/Quantum/Reversible/Sampling.lean)
and its [resource API](../../CslibFrontier/Computability/Circuit/Quantum/Reversible/Sampling/Resources.lean).
For `s = count * width` seed bits, `G` Boolean gates, and `m = n` outputs, it uses exactly
`s + G + 1 + m` active qubits, at most `s + 3 * G + m` elementary gates, and zero coherent
queries. It retains the seed and gate garbage, copies a fresh output block, and measures that
block once at the end; the final measurement is separate from `OracleCircuit.Resources`. The
encoded-code bound charges framed unary wire indices for the emitted gates. It does not charge
the static generator description or offline generation time as online attack execution.

[`HQC/SupportCircuit/Family.lean`](../../CslibFrontier/Crypto/Primitives/HQC/SupportCircuit/Family.lean)
builds a native uniform family from arbitrary polynomial-time word-width, value-bit, universe and
support-weight schedules. At every parameter its output has exactly the finite implemented law
above. Negligibility is a separate growing-width property; in particular, the published fixed
word width `32` does not satisfy it. The module records exact online resources and separate
polynomial offline-generator and static-occurrence accounting.

The generic family does not bind schedules to named HQC parameter sets or compose the multiple
support draws used by key generation and encryption. HQC v5.1 §6.2.3 also composes the
upper-density factors for three encryption support vectors multiplicatively; that integration is
tracked by [#5279](https://github.com/cslib-community/cslib-frontier/issues/5279), and the reduction
remains [#5281](https://github.com/cslib-community/cslib-frontier/issues/5281). The family module
makes no HQC security or QROM claim.

The complete ordinary clients in
[`HQCSupportCircuit.lean`](../../CslibFrontierTests/Crypto/HQCSupportCircuit.lean) and
[`HQCSupportProbability.lean`](../../CslibFrontierTests/Crypto/HQCSupportProbability.lean) check
the non-dyadic sampler law, finite discrepancy, and the growing-width qualification.
[`HQCSupportSamplerFamily.lean`](../../CslibFrontierTests/Crypto/HQCSupportSamplerFamily.lean)
checks an inhabited fixed-weight output for one generic schedule, the negligible growing-width
condition, each resource coordinate, and offline occurrence accounting. From the repository root,
build them with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.HQCSupportCircuit CslibFrontierTests.Crypto.HQCSupportProbability CslibFrontierTests.Crypto.HQCSupportSamplerFamily
```

Import [`HQC/Syndrome.lean`](../../CslibFrontier/Crypto/Primitives/HQC/Syndrome.lean) for the
finite 2-QCSD-P/2-DQCSD-P and 3-QCSD-PT/3-DQCSD-PT distributions from Definitions 2.3.6–2.3.9,
pp. 12–13. `realSyndromeLaw` draws the public circulant generator uniformly at its prescribed
parity and draws both secret blocks uniformly at fixed weight. Its comparison law keeps both the
public parity and the syndrome parity; a full-cube uniform comparison has a one-bit parity test.
`realTruncatedSyndromeLaw` uses one shared third secret block in both syndromes and retains the
requested prefix of the second. `mem_support_realTruncatedSyndromeLaw_iff` exposes that shared
witness explicitly. The comparison law keeps the first syndrome parity and samples the retained
second component from the full cube, exactly as the source does.

`eval_idealSupport_map_indicatorVector` connects the sampler above to these distributions: the
indicator of an ideal uniform fixed-cardinality support is exactly a uniform fixed-weight bit
string. The [checked syndrome examples](../../CslibFrontierTests/Crypto/HQCSyndrome.lean) cover
zero and full weight, detect a comparison distribution with the wrong parity baseline, and give a
four-bit sample that an incorrect independent redraw of the third secret accepts but the shared
law rejects. These are distribution definitions and exact finite laws, not assumptions that
2-QCSD-P or 3-QCSD-PT are hard.

Import [`Computational/HQC/DQCSD.lean`](../../CslibFrontier/Crypto/Computational/HQC/DQCSD.lean)
to state that these exact source distributions are indistinguishable to the native quantum word
tests above. `SyndromeSample.toWord` encodes the public block followed by the syndrome in `2n`
bits. `TruncatedSyndromeSample.toWord` encodes both public blocks, the complete first syndrome,
and the retained prefix of the second in `3n + (n - ell)` bits; both encodings are injective.
`NativeQuantumTwoDQCSDP` and `NativeQuantumThreeDQCSDPT` are the resulting asymptotic assumptions,
and their `of_within` theorems transfer concrete bounds with separate qubit, gate, query, and
exact encoded-description budgets. The four `*_iff_*` theorems expose both source-named assumptions through the shared
`NativeQuantum.IndistinguishableWithin` and
`NativeQuantum.ComputationallyIndistinguishable` interfaces. The [checked
client](../../CslibFrontierTests/Crypto/HQCDQCSD.lean) is an ordinary module that instantiates
positive parameter families, checks both encodings and all four length contracts, runs the exact
two-block words through the generic native game, exercises both concrete bridges, and consumes all
four assumptions through those shared interfaces. This is original no-advice, no-useful-oracle
packaging of the cited distributions: it proves no DQCSD hardness, does not bundle the
specification's separate primitive-prime requirement, and adds no QROM, decoding-failure, or
HQC-PKE/KEM security result.

The word-source model assumes independence and uniformity; it does not establish them for an
XOF. Positions use natural numbers, with checked 16-bit representability conditions for the
published parameter sets; byte serialization, native runtime, decryption-failure bounds and
HQC security remain separate obligations under the [post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

Import [`DuplicatedReedMuller.lean`](../../CslibFrontier/Foundations/Data/Code/DuplicatedReedMuller.lean)
for HQC v5.1's actual `RM(1, 7)` inner code and deterministic Hadamard decoder. `RMMessage` puts
the affine constant in byte bit 7 and the seven binary-column coefficients in byte bits 0–6;
`drmEncode` repeats each 128-bit word with multiplicity 3 for HQC-1 or 5 for HQC-3/HQC-5, giving
the source's `[384, 8, 192]` and `[640, 8, 320]` codes. `drmDecode_isNearestDecoder` proves that
the source's strict smallest-peak scan returns a nearest codeword, and
`drmDecode_add_eq_of_two_mul_weight_lt` recovers every message when twice the error weight is less
than `64 * μ`. The [checked clients](../../CslibFrontierTests/Code/DuplicatedReedMuller.lean)
exercise source bit order, both coefficient signs, equal-magnitude ties, exact distances and
nonzero errors. The shortened Reed–Solomon outer decoder, its composition with this inner code,
and the numerical decryption-failure calculation remain open.

Import [`HQC/PKE.lean`](../../CslibFrontier/Crypto/Primitives/HQC/PKE.lean) for the ideal
post-expansion algebra of HQC-PKE (§3.6, pp. 38–40). `PKEParams` records the ring, message and
retained-codeword lengths, the three fixed weights and the decoder radius. `pkeKeyGen` draws
fixed-weight `y`, then `x`, followed by a uniform public ring word `h`, publishing
`(h, s = x + circulant h *ᵥ y)` while retaining expanded `y`; `pkeSampleCoins` draws `(r₂, e, r₁)` in
the source order. `pkeEncrypt` and `pkeDecrypt` implement the two source algorithms with
`truncate P` retaining exactly the first `n - ℓ` bits, and `toExplicitCoinPKE` supplies the
shared explicit-coin PKE interface used by the Fujisaki–Okamoto transform.

The central checked identity `pkeDecryptInput_encrypt` says that the decoder sees `Encode(m)` plus
the retained prefix of `x * r₂ - r₁ * y + e` (the minus sign is addition over `Bool`). Its proof
uses `circulant_mulVec_comm` and `circulant_mulVec_assoc` to cancel the two public-`h` terms.
`pkeDecrypt_encrypt_eq_of_weight_le` then consumes the plain encoder/decoder contract
`DecoderCorrects` and a retained-error weight bound. The
[checked client](../../CslibFrontierTests/Crypto/HQCPKE.lean) uses positive weights and proper
one-bit truncation, proves a length-three repetition decoder corrects one error, refutes the same
contract for a constant decoder, checks key/coin support and runs the packaged PKE.

Import [`Computational/HQC/INDCPA.lean`](../../CslibFrontier/Crypto/Computational/HQC/INDCPA.lean)
for the exact finite game argument in HQC v5.1, Theorem 6.3 and Equation (10), printed pp. 61–64.
`indCpaGame` uses the shared `TwoStage` interface: after seeing the expanded public key, the first
stage chooses both messages and a saved state, so the challenge messages may depend on that key.
This is strictly more faithful to the source game than the fixed-message
`ExplicitCoinPKE.indCpaAdvantage` experiment. `eval_indCpaGame_eq_twoRealGame` identifies Game1
with the real 2-DQCSD-P reduction game; `twoUniformGame_eq_threeRealGame` identifies Game2 with
the real 3-DQCSD-PT reduction game; and `threeUniformGame_eq_uniform` proves that the comparison
game is a fair hidden-bit game because its uniform retained component masks the selected encoded
message. The resulting `indCpaAdvantage_le` bound is
`AdvIND-CPA ≤ Adv2-DQCSD-P + Adv3-DQCSD-PT`.

The public parity `b₁` is sampled from the public word, so both reduction laws explicitly mix
the two fixed-parity branches. The second identity also requires `omegaE = omegaR`; all published
v5.1 parameter sets have that equality, while `PKEParams` deliberately permits other finite
instances. The source's Definition 2.4.1 (printed p. 13) and the Lean definition both use the
absolute bias `|Pr[win] - 1/2|`. There is also a source inconsistency: the displayed Game3
body on printed p. 63 repeats Game2's fixed-weight sampling, whereas the adjacent transition text,
the 3-DQCSD-PT definition and the proof paragraph use the uniform comparison law and conclude that
the challenge bit is hidden. The formal game follows that stated comparison-law transition.

This is not yet an asymptotic native-quantum PKE security endpoint. The specification supplies no
gate, query or runtime loss for the two reductions, so connecting these finite advantages to the
canonical `NativeQuantumTwoDQCSDP` and `NativeQuantumThreeDQCSDPT` assumptions still needs
encoded-circuit/resource certificates and an explicit fair-mixture handoff. The [checked ordinary
client](../../CslibFrontierTests/Crypto/HQCINDCPA.lean) uses positive weights, proper truncation and
key-dependent challenge messages, then applies all three identities and the final bound.
Production seed/XOF expansion, the biased sampler, Theorem 6.4's salted Fujisaki–Okamoto/QROM
argument, IND-CCA2 and complete HQC-KEM security remain out of scope.

Import [`HQC/Correctness.lean`](../../CslibFrontier/Crypto/Primitives/HQC/Correctness.lean) for
the decryption-failure bridge from Definition 6.2.1 and Equations (11), (13) and (14), §6.2.2,
pp. 64–65. The definition, Equations (11)/(13), and the source's exact-failure sentence are on
p. 64; Equation (14) is on p. 65. `pkeFullNoiseFailureExperiment` samples `y`, `x`, then
`(r₂, e, r₁)` and tests
whether the complete word `x * r₂ - r₁ * y + e` has weight greater than `Δ`.
`pkeDeltaCorrect_fullNoiseFailureProbability` proves that the packaged PKE is `δ`-correct at
exactly that experiment's real probability: its left side is still the expectation over generated
keys of the worst failure probability over messages. `pkeDeltaCorrect_of_fullNoiseFailureProbability_le`
accepts any proved real upper bound on that probability.

For numerical bounds, `pkeKeyGen_expect` and `pkeSampleCoins_expect` expose the two independent
key draws, uniform public word, and three independent encryption draws in their source order while
the sampler implementations stay opaque. `pkeFullNoiseFailureMass_eq_iterated_expect` presents
Equation (14) directly as five nested expectations of its event indicator, and
`pkeFullNoiseFailProb_eq_iterated_expect` gives the corresponding three-draw law for fixed key
witnesses. Bounds proved with the ordinary expectation monotonicity API therefore feed directly
through `pkeFullNoiseFailureProbability_eq_toReal_mass` and
`pkeDeltaCorrect_of_fullNoiseFailureProbability_le`.

The source event is a conservative upper bound here because decryption sees only the retained
prefix and `weight_truncate_le` proves that restriction cannot increase weight. The formalization
does not assert the source's stronger “if and only if” sentence: `DecoderCorrects` guarantees success
inside the decoding radius but does not say every larger error fails. The
[correctness client](../../CslibFrontierTests/Crypto/HQCCorrectness.lean) applies the bridge to the
repetition-code fixture and checks a positive-weight one-bit instance where the full-noise failure
probability is exactly one.

This module does not replace the source's seeds and XOF with a proved implementation model, build
the concatenated Reed–Muller/Reed–Solomon codec, establish primitive-prime admissibility or a
numerical DFR bound for the published parameter sets, or prove IND-CPA, Fujisaki–Okamoto or KEM
security. These modules are therefore correctness prerequisites, not an HQC security endpoint.

### SDitH binary regular syndrome decoding

Import [`RegularSyndrome.lean`](../../CslibFrontier/Foundations/Data/Code/RegularSyndrome.lean)
for the binary regular-syndrome relation from the
[SDitH v3.0 specification](https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/SDitH_specifications.pdf),
§2.2 (pp. 8–9) and Algorithms 1–2 (pp. 12–13). Coordinates have type
`Fin chunks × Fin chunkSize`, so the word is visibly partitioned into equal chunks.
`regularWord positions` uses `Pi.single` to put one `true` at the selected position of every
chunk; `IsRegularWord x` reuses `Cslib.BitString.IsSingle` for each chunk, and the shared
`hammingNorm_eq_one_iff_isSingle` theorem connects that representation to Hamming weight one. Then
`IsRegularSyndromeSolution H y x` adds the existing `Cslib.Code.syndrome H x = y`
relation. These reusable definitions and theorems live in `Cslib.Code` beside the parity-check
API; they are not computational-hardness assumptions.
`IsRegularWord.hammingNorm_eq` proves that every such word has total weight `chunks`.

The [checked client](../../CslibFrontierTests/Crypto/SyndromeDecoding.lean) uses two chunks of
length three and a parity-check matrix whose rows sum the respective chunks. It verifies a
nonzero regular witness with syndrome `11` and rejects the zero word. Build it with
`lake build CslibFrontierTests.Crypto.SyndromeDecoding`.

This is only the reusable binary RSD relation. It does not model seed expansion, the PIOP,
commitments, grinding, signing or verification, and it states no hardness or unforgeability
claim. In particular, SDitH v3.0 §5.1 uses a heuristic uniqueness estimate in its advertised
SD-to-RSD loss, and §5.3 defers a formal EUF-CMA proof to a future version. Those obligations and
the quantum-security endpoint remain open under the
[post-quantum program](https://github.com/cslib-community/cslib-frontier/issues/4987).

### SDitH tweakable salt domain separation

Import [`TweakSalt.lean`](../../CslibFrontier/Crypto/Primitives/SDitH/TweakSalt.lean) for
SDitH v3.0 Algorithm 5 (pp. 16–17). `tweakSalt variant salt tweak tag` copies a
`securityBits`-bit salt, writes `tweak : Fin (2 ^ 24)` into the low 24 coordinates using
the existing little-endian `BitString.equivFin` convention, and writes the high tag bits
selected by hash- or cipher-based grinding. When `26 ≤ securityBits`, the 24 low tweak positions
and the two possible high tag positions are disjoint. Under that hypothesis, the low-, middle-,
and high-coordinate theorems expose the complete layout, and `tweakSalt_injective` shows that a
fixed salt and variant retain the tweak/tag pair. The definition remains total below this bound
with the source's assignment order: at width 25 the cipher tag overwrites tweak bit 23, so tweaks
`5` and `5 + 2^23` collide for the same tag. The
[ordinary-module client](../../CslibFrontierTests/Crypto/SDitH/TweakSalt.lean) checks overwritten
low bits, preserved middle bits, both high layouts, distinct tweaks and tags, and injectivity at
the 128-bit NIST width.

Algorithm 6's counter-mode byte PRG is a separate source consumer and remains unimplemented.
This function-level layout also has no native machine or resource certificate: later work must
account for materializing the full salt, the 24-bit conversion and tag updates, the number of calls
made by PRG/tree expansion, and the resulting time, output-size, program-size, and
reduction-resource translations.

### SDitH two-child seed expansion

Import [`ExpandSeed.lean`](../../CslibFrontier/Crypto/Primitives/SDitH/ExpandSeed.lean) for the
five-line `ExpandSeed` procedure in SDitH v3.0 §3.2.2 (p. 18). A node
`idx : Fin (2 ^ 23)` has exact 24-bit child tweaks `2 * idx` and `2 * idx + 1`, so neither wraps.
`expandSeed encStar variant salt seed idx` applies the explicit modified-cipher parameter
`encStar` under `seed` to the two `tweakSalt` plaintexts with tag `true`. Projection lemmas expose
both calls, while `expandSeed_plaintexts_ne` proves that their plaintexts differ when
`26 ≤ securityBits`; it intentionally does not assert that the encrypted child seeds differ. The
[ordinary-module client](../../CslibFrontierTests/Crypto/SDitH/ExpandSeed.lean) checks both numeric
tweaks and both outputs of a concrete 128-bit XOR toy cipher.

The specification labels this procedure for Categories I and V. The current reference code also
contains a 192-bit Category III path using truncated Rijndael-256-256, but that implementation
observation is not silently promoted to a source claim here. The API is primitive-parametric and
proves no AES/Rijndael, PRP/ICM, TreePRG, soundness, zero-knowledge, or signature theorem. At the
function level it makes exactly two modified-cipher calls and materializes two full tweaked salts.
Later work must retain those time, space, randomness/query and output costs together with the
constructed program's description size and embedded parameters/advice; offline compiler
construction is a separate resource. Algorithm 6, the full GGM/BAVC tree, `CommitSeed`, the
protocol and transcript, abort and rejection analysis, Fiat–Shamir/QROM, SD/RSD hardness, and both
asymptotic and finite concrete endpoints remain open.

### Blinded Diffie–Hellman problems

Boneh–Shoup Lemmas 21.7 and 21.8 ([bs23][bs23], Section 21.11.5, pp. 910–911) show that two
problems, which the book uses in its informal argument for protocol PAKE2, are hard under CDH: each
proof turns an adversary for the problem into a CDH adversary. The book names neither
problem; "blinded CDH" and "two-point blinded CDH" are this library's names.
[`DiffieHellman/Blinded.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/Blinded.lean)
states both in one group, like `cdhExperiment`, for a `ZMod q`-module `G` with `[NeZero q]` and
`[DecidableEq G]`. `blindedCDHExperiment` asks for an exponent `γ` and
the value `blindedDH α x γ b v = (x - γ * α) • (v - γ • b)`, which is the book's
`[u / a^γ, v / b^γ]` written through the exponents of `u` and `a`. `blindedCDHPairExperiment` asks
for two distinct exponents, any `v` and both values. With exactly uniform blinding exponents,
Lemma 21.7 is the equality `cdhAdvantage_blindedCDHToCDH` for every such `q`, `G` and `g`, with no
further hypothesis; Lemma 21.8 is the inequality `blindedCDHPairAdvantage_le_cdhAdvantage`, which
also takes `[Fact q.Prime]`.
[`DiffieHellman/BlindedFamily.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/BlindedFamily.lean)
gives the family games `blindedCDHGame` and `blindedCDHPairGame`, the reductions
`blindedCDHToCDHAdversary` and `blindedCDHPairToCDHAdversary` with their certificates
`isPPT_blindedCDHToCDHAdversary` and `isPPT_blindedCDHPairToCDHAdversary` (each reduction is PPT
when its adversary is), their `sampleExp` losses `2 / 2 ^ n` and `1 / 2 ^ n`, and the conclusions
`CDH.negligible_blindedCDHGame` and `CDH.negligible_blindedCDHPairGame`: from `F.CDH setup` and an
adversary with `IsPPT`, its success probability in the game is negligible. The
[blinded CDH client](../../CslibFrontierTests/Crypto/BlindedCDH.lean) checks the algebra in
`ZMod 7`, a `ZMod 4` instance showing that `BlindedCDHPairAnswer.solve_eq`, the step of the
Lemma 21.8 reduction that recovers the CDH value, needs a prime order, and both theorems on PPT
adversaries. Check it with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.BlindedCDH
```

### The list form of CDH

In the argument for protocol PAKE1 ([bs23][bs23], Section 21.11.4, p. 908) and in the proof of
Theorem 11.4 ([bs23][bs23], Section 11.5.1, pp. 446–448), an adversary's random-oracle queries
give a list of candidates for the Diffie–Hellman value, and the CDH adversary, which cannot
recognize the right one, outputs one of them chosen at random. In Theorem 11.4 this is the source
of the factor `Q`: equation (11.12) reads `CDHadv[Bcdh, G] ≥ Pr[Z] / Q`. The book names neither
the problem nor the reduction; "list CDH" and the declaration names are this library's.
[`DiffieHellman/ListCDH.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/ListCDH.lean)
states it in one group, like `cdhExperiment`, for a `ZMod q`-module `G` with `[NeZero q]` and
`[DecidableEq G]`. In `listCDHExperiment q g Q A` the adversary `A : G → G → ProbComp (List G)`
receives `a • g` and `b • g` and wins when `(a * b) • g` is among the first `Q` entries of the list
it returns, which stands for the book's list of queries (at most `Q` of them in Theorem 11.4).
The reduction `listCDHToCDH g index A` runs `A`, draws a position from the index sampler
`index : ProbComp ℕ` and returns the entry there, or `g` when the position is past the end of the
list. The book's algorithm instead chooses among the queries it collected and, in Theorem 11.4,
reports failure when there are none. With `index = Fin.val <$> ProbComp.unifFin (Q - 1)`, exactly
uniform below `Q` when `0 < Q`, `listCDHAdvantage_le_mul_cdhAdvantage` gives
`listCDHAdvantage q g Q A ≤ Q * cdhAdvantage q g (listCDHToCDH g index A)` for every `Q`, every `A`
and every such `q`, `G` and `g`, with no further hypothesis: at `Q = 0` the list experiment is
never won (`listCDHAdvantage_zero`), a list shorter than `Q` counts in full, and repeated entries
are allowed. For any index sampler `index`, `eval_listCDHExperiment_le_mul_add_of_index` takes
a factor `c : ℝ≥0∞`, a term `ε : ℝ≥0∞` and the hypothesis `hindex`: for every list `l` and
every `x ∈ l.take Q`, `1 ≤ c * (ProbComp.eval index).map (fun i => l.getD i g) x + ε`. It shows
that the list experiment accepts with probability at most `c` times that of the CDH experiment
for `listCDHToCDH g index A`, plus `ε`, in `ℝ≥0∞`. Its proof averages the bound for each
list over the list and the two exponents with `PMF.bind_apply_le_mul_bind_apply_add` of
[`Probability/PMF/DensityBounds.lean`](../../CslibFrontier/Probability/PMF/DensityBounds.lean): for
`p : PMF α`, `f g : α → PMF β`, `c ε : ℝ≥0∞` and an outcome `b`, it takes
`h : ∀ a, f a b ≤ c * g a b + ε` and shows `p.bind f b ≤ c * p.bind g b + ε`, so the constant `ε`
is averaged, not multiplied; `PMF.bind_apply_le_mul_bind_apply` is its case `ε = 0`.
`eval_listCDHExperiment_le_mul` is the case `ε = 0`, with `hindex` read without `+ ε`, and
gives the bound with a factor `c` alone. The uniform case uses
`PMF.inv_le_map_uniformOfFintype_getD` of
[`Probability/PMF/UniformIndex.lean`](../../CslibFrontier/Probability/PMF/UniformIndex.lean): for
`[NeZero Q]`, any list `l`, any default `d` and `hx : x ∈ l.take Q`, an index uniform on `Fin Q`
read in `l` with default `d` equals `x` with probability at least `(Q : ℝ≥0∞)⁻¹`.
A machine with fair coins cannot draw an exactly uniform position below every `Q`. The capped
residue sampler `ProbComp.sampleModIndex width bound` of
[`Languages/Probabilistic/UniformNat/ModIndex.lean`](../../CslibFrontier/Languages/Probabilistic/UniformNat/ModIndex.lean)
draws `ProbComp.sampleModNat width bound`, the residue modulo `bound` of a number written with
`width` fair coins, and caps it at `bound`. At `bound = 0` it returns `0`;
`ProbComp.sampleModIndex_eq_sampleModNat` takes `hbound : 0 < bound` and shows that the cap then
changes nothing. `Probability.isPPTOn_sampleModIndex`, in the
[certificate module](../../CslibFrontier/Computability/Probabilistic/UniformNat/ModIndex.lean),
takes an input encoding `input : α ↪ List Bool`, `hwidth : ComputableInPolyTime width input encUnary`
and `hbound : ComputableInPolyTime bound input encUnary`, and shows that the sampler is uniformly
strict PPT with unary output. The modular key-chain and leveled reductions of
[`Leveled/ExactSecurity.lean`](../../CslibFrontier/Crypto/Computational/Homomorphic/Leveled/ExactSecurity.lean)
draw their indices with the same sampler. `eval_listCDHExperiment_le_mul_add` takes this index in
one group: for a `ZMod q`-module `G` with `[NeZero q]` and `[DecidableEq G]`, and every `g`,
`width`, `Q` and `A`, with no further hypothesis, it shows in `ℝ≥0∞`

```lean
ProbComp.eval (listCDHExperiment q g Q A) true ≤
  Q * ProbComp.eval
      (cdhExperiment q g (listCDHToCDH g (ProbComp.sampleModIndex width Q) A)) true +
    Q / 2 ^ width
```

The factor is exactly `Q`. Each residue below `Q` is drawn with probability at least
`1 / Q - 1 / 2 ^ width`: `ProbComp.one_le_mul_eval_sampleModNat_add` of
[`Languages/Probabilistic/UniformNat/LowerBound.lean`](../../CslibFrontier/Languages/Probabilistic/UniformNat/LowerBound.lean)
takes `hi : i < m` and shows, for every `w`,
`1 ≤ m * ProbComp.eval (ProbComp.sampleModNat w m) i + m / 2 ^ w` in `ℝ≥0∞`. With the same
hypothesis and every `w`, `ProbComp.le_eval_sampleModNat_toReal` in that module states the bound in
`ℝ`: `(1 - m / 2 ^ w) * m⁻¹ ≤ (ProbComp.eval (ProbComp.sampleModNat w m) i).toReal`. A member
of the first `Q` entries of a list sits at a position `i` below `Q` and below the length of the
list, and the reduction returns it whenever it draws `i`, so
`eval_listCDHExperiment_le_mul_add_of_index` applies with `c = Q` and `ε = Q / 2 ^ width`. Short
lists and `Q = 0` need no separate case: only the positions of members count, and at `Q = 0` there
are none.

[`DiffieHellman/ListCDHFamily.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/ListCDHFamily.lean)
gives the family game `listCDHGame setup Q adversary` for a bound `Q : ℕ → ℕ` and the reduction
`listCDHToCDHAdversary width Q adversary`, which runs `listCDHToCDH` with the index
`ProbComp.sampleModIndex (width n) (Q n)` for a coin count `width : ℕ → ℕ`.
`ListCDHAdversary.IsPPT` asks for one uniform strict PPT machine from `encCDHInput` to the framed
list of the words of the entries. `isPPT_listCDHToCDHAdversary` certifies the reduction: it takes
`hwidth : ComputableInPolyTime width encUnary encUnary`,
`hQ : ComputableInPolyTime Q encUnary encUnary` and `hA : adversary.IsPPT`, and shows
`(F.listCDHToCDHAdversary width Q adversary).IsPPT`. `succProbability_listCDHGame_le` bounds the
loss for every `setup`, `width`, `Q`, `adversary` and `n`, with no further hypothesis, in `ℝ≥0`:

```lean
Game.succProbability (F.listCDHGame setup Q adversary n) ≤
  Q n * Game.succProbability
      (F.cdhGame setup (F.listCDHToCDHAdversary width Q adversary) n) +
    Q n / 2 ^ width n
```

The lift over `setup` averages the one-group bound over the drawn group description with
`PMF.bind_apply_le_mul_bind_apply_add`, as above. The certified loss is the book's factor `Q n`
and the additive term `ε = Q n / 2 ^ width n`, which is not zero for any `width n` when
`Q n ≠ 0`. In one group, `eval_listCDHExperiment_mono` takes `hle : Q ≤ Q'` and shows that the
list experiment with the bound `Q'` accepts with probability at least that with the bound `Q`.
`succProbability_listCDHGame_mono` lifts it over `setup`: it takes `hle : Q n ≤ Q' n` and shows
that the success probability at `n` with the bound `Q'` is at least that with the bound `Q`. The
conclusion `CDH.negligible_listCDHGame` takes `h : F.CDH setup`, `hQ` and an adversary with
`hA : adversary.IsPPT`, and shows that its success probability in the list game is negligible;
its proof takes `width n = n`, and `ε = Q n / 2 ^ n` is negligible because `hQ` bounds `Q`
polynomially. The [list CDH client](../../CslibFrontierTests/Crypto/ListCDH.lean) checks the
uniform bound in `ZMod 7` at `Q = 0`, at `Q = 1`, at `Q = 3` beyond the length of the list and
with a repeated solution, the reduction's output past the end of the list, the general bound with
a deterministic index with and without a term, the fair-coin bound at `Q = 0` and at `Q = 3`,
monotonicity from `Q = 1` to `Q = 3`, the sampler at the bounds `0` and `3` with its certificate,
and both lower bounds on `sampleModNat` with `2` coins and modulus `3`. Over any family it checks
the certificate, the loss bound and the conclusion with `width n = n` and `Q n = n`, the loss bound
with `Q n = 0` and with `Q n = 3`, and monotonicity in `Q`; the conclusion also on Schnorr groups.
Check it with:

```bash
scripts/build.sh --wfail --iofail CslibFrontierTests.Crypto.ListCDH
```

## Encryption and chosen-message attacks

[AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/Basic.lean#L73) has a first stage choosing two messages and a saved word from the public key, and a second stage guessing from that saved state and the challenge ciphertext. Each stage has a native certificate. `INDCPAOn` explicitly constrains admissible message pairs. `WordINDCPA` requires equal lengths; the general `INDCPAOf` with all pairs is stronger for variable-length word messages. Invalid challenges are made independent of the hidden experiment bit. `Encryption.advantage (gameOn valid keyGen encrypt adversary) n` names the advantage between the two sides of the experiment at parameter `n`, and `INDCPAOn` asks that it be negligible for every admissible adversary; bounds on other two-sided encryption experiments, such as the DEM and CCA games, are stated with the same name.

To state a security reduction for one fixed scheme, without words or a security parameter, import
[`Encryption/Scheme.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Scheme.lean).
`PKE PK SK M C` has typed keys, messages and ciphertexts (`keyGen`, `encrypt`, and `decrypt`
returning `Option M`), `PKE.Correct` is perfect correctness, and
`E.cpaExperiment valid A b : Experiment` draws a key pair and runs the left-or-right experiment
`lrExperiment` of [`TwoStage.lean`](../../CslibFrontier/Crypto/Computational/TwoStage.lean) on the
public key, against a `TwoStage` adversary with any state type. Bound
`Experiment.advantage (E.cpaExperiment valid A false) (E.cpaExperiment valid A true)` by a
reduction's advantage at a fixed instance, then pass to the word level:
`Encryption.gameOn_eq_cpaExperiment` says that `gameOn valid keyGen encrypt adversary bit n` is
the typed experiment of the scheme with key generation `keyGen n` and encryption `encrypt n`,
played by `adversary.toTwoStage n`. Rewrite advantages with
`Encryption.advantage_gameOn_eq_cpaExperiment`: `Encryption.advantage` applies `gameOn`
partially, so `rw` with the experiment equation does not reach it. `AdversaryOf.isPPT_toTwoStage`
turns a word-level PPT certificate into a `TwoStage.IsPPT` family. For chosen-plaintext attacks
with an encryption oracle, import
[`Encryption/PublicKeyCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyCPA.lean):
the stages of a `PKE.CPAOracleAdversary` are oracle programs over the typed oracle
`E.encrypt pk`, and `PKE.cpaOracleExperiment_eq_cpaExperiment` rewrites
`E.cpaOracleExperiment valid A b` into `E.cpaExperiment valid (A.toTwoStage E) b`, where
`A.toTwoStage E` answers the queries itself under the public key it saved
([katzlindell20][katzlindell20], Proposition 12.3, at one scheme). At parameter `n`,
`Encryption.cpaOracleGameOn_eq_cpaOracleExperiment` says that the word-level game is this typed
experiment, played by `adversary.toCPAOracleAdversary n`. The
[checked examples](../../CslibFrontierTests/Crypto/PKEScheme.lean) separate the two challenge
bits of a key-leaking scheme, with and without the oracle, and rewrite `gameOn` and
`cpaOracleGameOn` into the typed experiments; run
`scripts/build.sh CslibFrontierTests.Crypto.PKEScheme`. The PPT transfer is checked in
[`CslibFrontierTests/Crypto/Experiment.lean`](../../CslibFrontierTests/Crypto/Experiment.lean).

For functional encryption at one fixed scheme (Boneh–Shoup v0.6, Section 15.7, Definitions 15.13 and 15.15, Attack Game 15.9, Example 15.1 and Remark 15.13, pp. 658–661 [bs23][bs23]), import [`Encryption/Functional.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Functional.lean). `FE MPK MSK Fn SK M C Y` packages `setup`, `keyGen`, `encrypt` and deterministic `decrypt`, and `FE.Functionality Fn M Y` bundles `eval : Fn → M → Option Y` with the null identifier `null : Fn` (`ε`); `FE.Correct` and `FE.Robust` state correctness and ciphertext robustness. Both `eval` and `decrypt` return `Option Y`, using `none` for `⊥` in `eval` and for both `⊥` and rejection in `decrypt`, so the book's robustness implies `FE.Robust` while the converse can fail for a scheme that outputs `⊥` where the functionality has a value. In `E.ssExperiment F A b`, the challenger generates `(mpk, msk)` and `skNull ← E.keyGen msk F.null`, runs the two stages of `A : FE.Adversary MPK Fn SK M C σ` against the logged key-generation oracle `E.keyGen msk` (`ProbOracleComp.runLog`, with `ProbOracleComp.runLog_sample` in [`Oracle/RunState.lean`](../../CslibFrontier/Languages/Probabilistic/Oracle/RunState.lean)) around a single challenge encryption, and enforces the query restriction at the end by returning `guess && F.admissible ((log₁ ++ log₂).map Prod.fst) pair`, so any run in which `F.null` or a pre- or post-challenge key query distinguishes the challenge messages outputs `false` in both experiments. When `F.eval F.null` is injective, `FE.eval_ssExperiment_eq_of_injective_null` and `FE.advantage_ssExperiment_eq_zero_of_injective_null` (specialized to `FE.Functionality.pke` in `FE.advantage_ssExperiment_pke_eq_zero`) show that every scheme—including the cleartext scheme `FE.cleartext F` (`FE.cleartext_correct`, `FE.cleartext_robust`)—has semantic-security advantage `0` against every adversary (Remark 15.13). For a public-key scheme `E : PKE PK SK M C`, `E.toFE leak` implements Example 15.1 over `FE.Functionality.pke len`, with correctness characterized by `PKE.toFE_correct_iff`, and `PKE.eval_ssExperiment_toFE_ofTwoStage` shows that against `FE.Adversary.ofTwoStage A` (which makes no key queries; this compares the two experiments and is not a reduction or efficiency claim) the game coincides with `E.cpaExperiment` with admissibility rule `len m₀ = len m₁`. Asymptotic security over scheme families and efficient typed oracle adversaries (Definition 15.14), identity-based encryption (Example 15.2), and Exercises 15.21–15.22 are not formalized here. The [checked examples](../../CslibFrontierTests/Crypto/FunctionalEncryption.lean) exercise `FE.cleartext`, `FE.Robust`, pre- and post-challenge key queries, Remark 15.13 and `PKE.toFE`; run `scripts/build.sh CslibFrontierTests.Crypto.FunctionalEncryption`.

To replace the honest public-key distribution by another law, such as lossy or uniform keys, import
[`Encryption/PublicKeyReplacement.lean`](../../CslibFrontier/Crypto/Computational/Encryption/PublicKeyReplacement.lean).
`publicKeyGameOn valid keys encrypt adversary bit n` is `gameOn valid` with its public key drawn
from `keys` (`eval_gameOn_eq_publicKeyGameOn`). `keyDistinguisherOn valid encrypt adversary` is the
single hidden-bit reduction between two key laws, and `advantage_publicKeyGameOn_le` bounds the
chosen-message advantage under the real law by twice its advantage plus the advantage under the
replacement law. `isPPT_keyDistinguisherOn` certifies it from a polynomial-time `valid`, native
encryption and a PPT adversary. The unrestricted names `publicKeyGame`, `keyDistinguisher`,
`eval_game_eq_publicKeyGame`, `isPPT_keyDistinguisher` and `advantage_publicKeyGame_le` are the
`valid := fun _ _ _ _ => true` case. Goldwasser–Micali uses both forms (single bits and bounded
words); Regev, dual Regev and GSW use the unrestricted one. A proof that unfolds `publicKeyGame` or
`keyDistinguisher` also unfolds `publicKeyGameOn` or `keyDistinguisherOn`, plus `↓reduceIte` under
`simp only`. The orientation, factor-two and inadmissible-pair checks are in
[`CslibFrontierTests/Crypto/GSWSecurity.lean`](../../CslibFrontierTests/Crypto/GSWSecurity.lean).

For adaptive `Q`-query left-or-right chosen-plaintext attacks (Boneh–Shoup Section 11.3.2, Attack Game 11.2 and Definition 11.4, p. 439; cf. Attack Game 11.1, Section 11.2, p. 436 [bs23][bs23]), import [`Encryption/LoRCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/LoRCPA.lean). `LoRAdversaryOf Msg` (`LoRAdversary := LoRAdversaryOf Bool`, `WordLoRAdversary := LoRAdversaryOf (List Bool)`) has `start`, `query` (which receives the saved state word and ciphertext transcript and returns the next challenge pair `(m₀, m₁)` together with the updated saved state word), and `guess`, with `LoRAdversaryOf.IsPPT` charging a polynomial per-step growth bound `state_growth` on the saved state across the `Q n` adaptive rounds (`lorStepOn`, `lorRunOn`, `lorDistinguisherOn`, `lorKeyDistinguisherOn`, `lorGameOn`, `LoRINDCPAOn`, `isPPT_lorDistinguisherOn`, `isPPT_lorKeyDistinguisherOn`, `advantage_lorDistinguisherOn_le`, their unrestricted specializations `lorStep`, `lorRun`, `lorDistinguisher`, `lorKeyDistinguisher`, `lorGame`, `LoRINDCPAOf`, `LoRINDCPA`, `isPPT_lorDistinguisher`, `isPPT_lorKeyDistinguisher`, `advantage_lorDistinguisher_le`, and `WordLoRINDCPA` under the equal-length rule `m₀.length == m₁.length`).

[CCA2AdversaryOf](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Encryption/CCA.lean#L266) exposes adaptive decryption before and after the challenge; the second handler rejects the exact challenge ciphertext. The multi-challenge interface in [`CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA.lean) (`MultiCCA2AdversaryOf`, `INDCCA2MultiOn`) is a two-phase **batch** model, whereas [`CCA/Interleaved.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean) (`InterleavedCCA2AdversaryOf`, `interleavedCcaOracle`, `INDCCA2InterleavedOn`) formalizes Boneh–Shoup Attack Game 12.1 and Definition 12.1 ([bs23][bs23], §12.1, pp. 467–468) with a single stateful combined encryption-and-decryption oracle that tracks the list `S` of challenge ciphertexts generated so far, allowing arbitrary adaptive interleaving of `.challenge m₀ m₁` and `.decrypt c` queries (including decryption of a ciphertext `c` before a later challenge happens to produce `c`) and proving equivalence with both 1CCA and phased batch multi-challenge CCA (`indcca2InterleavedOn_iff_indcca2On`, `indcca2InterleavedOn_iff_indcca2MultiOn`, and `advantage_interleavedCca2GameOn`, with concrete checks in [`CslibFrontierTests/Crypto/CCAInterleaved.lean`](../../CslibFrontierTests/Crypto/CCAInterleaved.lean)). Encodings are part of the security boundary: the inspected Cramer–Shoup parser [decodeCramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup/Scheme.lean#L876) requires canonical framing, so a different raw serialization of the challenge does not silently bypass the equality check.

A malleable scheme is not CCA secure: an adversary maps the challenge to a different ciphertext with a related plaintext, asks the Phase 2 oracle to decrypt it, and reads off the hidden bit (Boneh–Shoup v0.6, Section 12.2.1, pp. 469–470 [bs23][bs23]). [`CCA/Malleability.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CCA/Malleability.lean) packages this attack once. `maulAdversary msg₀ msg₁ maul target` chooses the pair, queries `maul n pk ct` once and compares the reply with `target n pk`. `isPPT_maulAdversary` certifies it from polynomial-time ingredients. `not_indcca2On_of_maulAdversary` refutes `INDCCA2On` when the pair is admissible under honest keys and, on every honest key pair and challenge ciphertext, the transformation changes the decryption and decrypts to `target` exactly in world `1`; the oracle then cannot reject the query, and the advantage is exactly `1` (`advantage_cca2GameOn_maulAdversary`). A scheme supplies only these conditions: [`GoldwasserMicali/Malleability.lean`](../../CslibFrontier/Crypto/Computational/GoldwasserMicali/Malleability.lean) multiplies the challenge by the public nonresidue, which flips the bit (`not_indcca2_goldwasserMicali`, unconditional, and `not_indcca2_blumGoldwasserMicali` under the Blum condition of `indcpa_blumGoldwasserMicali`), and [`Paillier/Malleability.lean`](../../CslibFrontier/Crypto/Computational/Paillier/Malleability.lean) multiplies it by `1 + N`, which adds `1` to the plaintext (`not_indcca2On_paillier`, unconditional, for the scheme and predicate of `DCR.indcpaOn_paillier`), and multiplicative ElGamal (below) adds `g` to the second ciphertext component. Each scheme's CCA decryptor is its never-rejecting `decryptOpt`, and the `INDCCA2Interleaved…` corollaries follow by `INDCCA2InterleavedOn.indcca2On`. The [checked clients](../../CslibFrontierTests/Crypto/CCAMalleability.lean) pair each IND-CPA theorem with its CCA failure and run both attacks on concrete moduli; run `scripts/build.sh CslibFrontierTests.Crypto.CCAMalleability`.

The endpoint [DDH.indcca2On_cramerShoup](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/CramerShoup.lean#L1688) (together with its batch multi-challenge lift `DDH.indcca2MultiOn_cramerShoup` and fully adaptive interleaved multi-challenge lift [`DDH.indcca2InterleavedOn_cramerShoup`](../../CslibFrontier/Crypto/Computational/CramerShoup/Interleaved.lean)) combines DDH, collision resistance, negligible inverse group order, and explicit efficient public operations. Key generation draws a uniform hash key and publishes it in the public key, as Cramer and Shoup do ([cs03][cs03], Section 6.1, Figure 1), so the collision-resistance premise is about a keyed family: its collision finders see the group and the key. A premise about one fixed hash per security parameter would not be the standard notion, since for a fixed function an adversary that just outputs a collision exists (Boneh–Shoup v0.6, Section 8.1, p. 290 [bs23][bs23]). The theorem assumes collision resistance, following Boneh–Shoup Theorem 12.9; the original papers need only target collision resistance (universal one-wayness) of the keyed hash ([cs03][cs03], Section 6.2, Theorem 1). Approximate modular sampling and its statistical error are accounted for. Other clients include ElGamal, hybrid encryption, authenticated encryption and encrypt-then-MAC; they instantiate the same staged/oracle security schemas. Homomorphic schemes add circuit functionality and are treated [separately](homomorphic-encryption.md).

IND-CPA security does not give CCA security. [`ElGamal/Malleability.lean`](../../CslibFrontier/Crypto/Computational/ElGamal/Malleability.lean) shows that multiplicative ElGamal, which is IND-CPA secure under DDH, is not CCA secure (Boneh–Shoup v0.6, Exercise 12.1, p. 512 [bs23][bs23]). The adversary `elGamalMaulAdversary` is `maulAdversary` with transformation `elGamalMaulCiphertext`, which maps the challenge `(v, e)` to `(v, e + g)`; it asks the Phase 2 oracle to decrypt that different ciphertext and compares the reply with `m₁ + g`. `isPPT_elGamalMaulAdversary` certifies it, and `advantage_cca2GameOn_elGamalMaulAdversary` gives advantage exactly `1` at every parameter. `not_indcca2Of_elGamalBitEncryptProb` needs only a polynomial-time group family; `not_indcca2On_elGamalGroupEncryptProb` covers group-element messages under any admissibility predicate that admits `(0, g)`, such as `cramerShoupValid`. In the CCA games the decryptor is `elGamalDecryptOpt`, which never rejects. The proofs supply only the malleability conditions to `not_indcca2On_of_maulAdversary`, which applies the `INDCCA2On` hypothesis to the adversary through `isPPT_maulAdversary` and contradicts negligibility with `not_negligible_const`. The [checked clients](../../CslibFrontierTests/Crypto/ElGamalMalleability.lean) run the attack on a Schnorr group; run `scripts/build.sh CslibFrontierTests.Crypto.ElGamalMalleability`.

The canonical [`KEMINDCPA keyLen keyGen encaps`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid.lean) compares the real encapsulated key with an independent uniform `keyLen n`-bit word. Use `fun n => n` for normalized keys, or another schedule such as `fun n => 2 * n`. The composition methods `KEMINDCPA.hybrid_indcpa` and `KEMINDCPA.hybrid_indcpaOn` consume `DEMOneTimeKeyINDCPAOf` and `DEMOneTimeKeyINDCPAOn` at the same schedule; the latter requires a polynomial-time admissibility predicate independent of the public key. The exact bound is twice the hidden-bit KEM distinguisher's advantage plus the DEM adversary's advantage (Boneh–Shoup v0.6, Exercise 11.9(b), pp. 460–461 [bs23][bs23]). The native ideal-game certificate `isPPTOn_kemIdealGame` additionally takes `ComputableInPolyTime keyLen encUnary encUnary`. The reductions do not sample ideal keys, so the security implication itself does not need that certificate.

For a fixed KEM and symmetric cipher, without words or a security parameter, import
[`Encryption/KEMDEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEMDEM.lean).
`KEM PK SK CT K` of [`Encryption/KEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEM.lean)
has typed `keyGen`, `encaps` and `decaps` returning `Option K`. `KEM.Correct` is perfect
correctness, and `E.cpaExperiment sampleKey D b` gives the distinguisher a `KEM.Challenge` whose key
is either the encapsulated key (`b = false`) or a fresh key from `sampleKey` (`b = true`).
`Cipher K M C` of [`Encryption/Cipher.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Cipher.lean)
is a symmetric cipher. `D.oneTimeExperiment sampleKey valid A b` is its one-time left-or-right
experiment under a key drawn from `sampleKey`.

The hybrid scheme is `E.hybrid D : PKE PK SK M (CT × C)`, and `KEM.hybrid_correct` derives its
correctness from that of its components. `KEM.advantage_hybrid_le_two_mul` bounds the advantage of
its `cpaExperiment` by twice the KEM advantage of `KEM.hybridHiddenBitDistinguisher D valid A`,
plus the one-time advantage of `KEM.hybridCipherAdversary E A`. `KEM.advantage_hybrid_le` is the
variant with two distinguishers.

The word-level `advantage_hybridGame_le_two_mul` and `advantage_hybridGame_le` are these bounds for
`wordKEM keyGen encaps decaps n`, `wordCipher encryptSym decryptSym n` and
`adversary.toHybridTwoStage n`. They follow through the bridges `eval_game_hybridEncrypt`,
`eval_kemRealGame_eq_cpaExperiment`, `eval_kemIdealGame_eq_cpaExperiment` and
`eval_demKeyGame_eq_oneTimeExperiment`.

The [checked examples](../../CslibFrontierTests/Crypto/KEMDEM.lean) combine a KEM that sends its
key in the clear with the one-bit one-time pad, and show that the pad has one-time advantage zero.
They also rewrite the word-level hybrid game into the typed experiment. Run
`scripts/build.sh CslibFrontierTests.Crypto.KEMDEM`.

Starting with the imports and local context in [`CslibFrontierTests/Crypto/HybridEncryption.lean`](../../CslibFrontierTests/Crypto/HybridEncryption.lean), `indcpaOf_hybridEncrypt_doubleKey_otp` shows the doubled-key composition; adjacent examples check native sampling, supported key lengths, correct decryption and the zero-width boundary. The unconditional security fixture discards its key and is explicitly not decryptable; decryption correctness is checked separately on a leaking KEM. Security does not bundle correctness, and the zero-width pad recovers only the empty message. For an actual cryptographic client, [`DDH.wordINDCPA_hybrid_hashedElGamal`](../../CslibFrontier/Crypto/Computational/ElGamal/ProbComp.lean) now accepts a `SecureKDF` and a standalone DEM at arbitrary `keyLen`; [`CslibFrontierTests/Crypto/DiffieHellman.lean`](../../CslibFrontierTests/Crypto/DiffieHellman.lean) instantiates the bridge with doubled key length. The security parameter controlling its modular-sampling error remains `n`, independently of the key length.

[`encryptKeyEncaps keyLen encrypt`](../../CslibFrontier/Crypto/Computational/Encryption/KEMFromPKE.lean) constructs a KEM from word public-key encryption by sampling a key and encrypting it (Boneh–Shoup v0.6, Exercise 11.9(e), p. 461 [bs23][bs23]). Apply `WordINDCPA.kemINDCPA_encryptKeyEncaps` with a native unary polynomial-time certificate for `keyLen`; the reduction chooses two equal-length keys, saves the public key and the first key, and preserves advantage exactly. The separate `isPPTOn_encryptKeyEncaps` certificate also needs native encryption, while `decrypt_encryptKeyEncaps` reuses the original total decryptor and its supported-ciphertext correctness. [`CslibFrontierTests/Crypto/KEMFromPKE.lean`](../../CslibFrontierTests/Crypto/KEMFromPKE.lean) provides complete checked clients, including composition of this constructor with the existing doubled-width one-time pad DEM, exact zero-width sampling, and a correctly decryptable but insecure key-revealing encryptor. No new failure/rejection behavior is added.

For adaptive decapsulation security, import [`KEMFromPKE/CCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEMFromPKE/CCA.lean) and apply `WordINDCCA2.indistinguishable_encryptKeyEncaps` (Boneh–Shoup v0.6, Exercise 12.5(f), p. 514 [bs23][bs23]). The result uses `Game.Indistinguishable` over `kemCCARealGame` and `kemCCAIdealGame`, with the existing `IsOraclePPT` adversaries. Both games share the CPA sampling continuations and use `cca2Phase2Oracle` to reject the exact challenge word. The reduction preserves advantage exactly, samples two equal-length keys, and forwards postchallenge queries unchanged. It requires a unary polynomial-time `keyLen`; honest algorithm certificates and supported-output correctness are separate. Here the original option-valued decryptor is retained, so `some []` denotes successful empty-key decapsulation and `none` denotes rejection.

The [checked CCA KEM clients](../../CslibFrontierTests/Crypto/KEMFromPKECCA.lean) instantiate doubled key length, an unconditional correct zero-width KEM, and a reply-dependent tag-flipping attack with advantage `1 - 2^(-keyLen n)`. The attack fixture is correctly decryptable but insecure; it makes no CPA-security claim. Its native oracle certificate bounds reply reading, and the honest-game certificate charges decryption. This KEM endpoint covers one encapsulation followed by adaptive queries. The composition below uses this schedule; prechallenge KEM queries and multiple encapsulation challenges remain separate objectives.

The canonical `hybridDecrypt` now takes Option-valued decapsulation and symmetric decryption,
rejects noncanonical ciphertext-pair encodings, and propagates component failures. Its supported
correctness theorem concludes `some msg`, preserving accepted empty keys and messages. The
native certificate charges the framing test and both callbacks. This repairs the representation
boundary needed by CCA composition, without changing `hybridEncrypt` or its CPA security
theorems.

[`Hybrid/DEMCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/DEMCCA.lean)
proves the exact DEM leg of Boneh–Shoup Exercise 12.5(a), p. 513 [bs23][bs23]. Its middle game
retains the original KEM key/encapsulation correlation and independently samples the actual
symmetric key distribution. The selected KEM component uses that key before and after the
challenge. A native reduction to the existing `SymmetricCipher.OneTimeINDCCA` game preserves
each experiment's output law, hence its advantage with factor one. Both challenge messages must
have length `n`, matching this symmetric-cipher model; invalid pairs return false in both worlds.
Canonical framing makes component-level challenge rejection agree with exact word rejection.

The [checked clients](../../CslibFrontierTests/Crypto/HybridDEMCCA.lean) include the existing PRF
Encrypt-then-MAC construction, a full-advantage echo-cipher counterexample, and a zero-width
adaptive trace distinguishing `none` from `some []`.

[`Hybrid/CompositionCCA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/Hybrid/CompositionCCA.lean)
completes both KEM hops and Exercise 12.5(a)'s concrete bound for this `n`-bit-message model:
`exists_hybridCCA_reductions` supplies native adversaries with hybrid advantage at most twice
the KEM advantage plus the actual symmetric CCA advantage. The hidden-bit reduction's signed
probability identities precede the absolute-value bound. `hybrid_indcca2On` gives the asymptotic
endpoint using existing `INDCCA2On`, and `isPPTOn_hybridCCAGame` certifies the honest experiment.
No new encryption scheme or security predicate is introduced.

The postprocessor `F` must take uniform `keyLen n`-bit seeds to exactly the distribution of
`E.keyGen n`, with one native algorithm for all parameters. The
[checked clients](../../CslibFrontierTests/Crypto/HybridCompositionCCA.lean) instantiate an actual
CCA-secure PKE's encrypted-key KEM with the PRF Encrypt-then-MAC cipher. Its `3*n` random bits
produce framed keys of encoded length `4*n+1`, not uniform encoded words. A general total
saved-coins client uses the existing evaluator theorem and returns supported keys on every seed.
Supported KEM correctness justifies the real-hop sampling commutation; perfect hybrid correctness
additionally checks support of the postprocessed real key. Tests expose the failure without that
KEM premise, and show that a perfect zero-width KEM with the insecure echo DEM remains insecure.
Arbitrary message-space extension and stronger KEM query schedules remain separate.

For the Diffie–Hellman random-oracle KEM of [katzlindell20][katzlindell20] (Construction 12.19,
Theorem 12.22), import
[`DiffieHellman/GapCDH.lean`](../../CslibFrontier/Crypto/Computational/DiffieHellman/GapCDH.lean).
It states the Gap-CDH game `PrimeOrderGroupFamily.gapCDHGame` (CDH with a
decisional Diffie–Hellman oracle, §12.4.4), the KEM `dhKEMEncaps` / `dhKEMDecaps`
with correctness `dhKEMDecaps_encaps`, and the IND-CCA game `dhKEMCCAGame` with a random-oracle
hash and a decapsulation oracle that refuses the challenge.
`advantage_dhKEMCCAGame_le` bounds the advantage of a deterministic oracle adversary by the
success probability of the explicit reduction `dhKEMToGapCDH`, with no additive term. The bound
is for one fixed group and an arbitrary finite key sampler; the asymptotic polynomial-time
statement is not yet proved. Checked clients are in
[`CslibFrontierTests/Crypto/GapCDH.lean`](../../CslibFrontierTests/Crypto/GapCDH.lean).

For explicit-coin public-key encryption and modular Fujisaki–Okamoto KEM transforms ([hhk17][hhk17],
ePrint 2017/604 full version dated 2 November 2021), import
[`PKE/ExplicitCoin.lean`](../../CslibFrontier/Crypto/Protocols/PKE/ExplicitCoin.lean) for the
generic scheme interface and
[`FujisakiOkamoto.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto.lean) for the
transform.
Unlike the word-level encryption interface used by `encryptKeyEncaps`, `ExplicitCoinPKE` (§2.1)
exposes a fixed coin type `R`, an arbitrary coin sampler `sampleCoins : ProbComp R` (where the
paper uses uniform draws and permits key-dependent `R`), and deterministic encryption
`encDet : PK → M → R → CT` alongside `keyGen` and `dec`, together with expected
worst-case-message `δ`-correctness `ExplicitCoinPKE.DeltaCorrect` (defined via `ProbComp.expect`
and `PMF.toOuterMeasure`, with `deltaCorrect_zero_of_perfect` and `DeltaCorrect.mono`),
`γ`-spreadness `ExplicitCoinPKE.GammaSpread`, and two-stage IND-CPA (§2.1 Def. 2.2 / Fig. 4):
`ExplicitCoinPKE.toPKE` is the randomized scheme as a `PKE`, and `ExplicitCoinPKE.cpaAdvantage` is
its advantage in the shared experiment `PKE.cpaExperiment` with every message pair admissible. The
advantage is the two-world difference, twice HHK17's `|Pr[b' = b] - 1/2|`. The narrower
fixed-message experiment `ExplicitCoinPKE.indCpaGame` (`ExplicitCoinPKE.indCpaAdvantage`, messages
`(m₀, m₁)` fixed before key generation, single-stage adversary) remains for the spread-necessity
example; the FO theorems and the K-PKE bound do not use it. On top of `ExplicitCoinPKE`, `FujisakiOkamoto.encT` and `FujisakiOkamoto.decT`
define the derandomization transform `T[PKE, G]` (§3.1, Fig. 5) with mandatory re-encryption check
`encT P G pk m' = c` (`decT_encT_eq_some`, `encT_of_decT_eq_some`, `dec_of_decT_eq_some`,
`decT_eq_none_of_reencrypt_ne`), while `FujisakiOkamoto.Scheme` (with arbitrary samplers
`sampleMsg` and `sampleKey`) packages both explicit-rejection `FO^⊥` (§3.2.1, Fig. 9;
`Scheme.encapsBot`, `Scheme.decapsBot`, `decapsBot_encT_eq_some`,
`decapsBot_eq_none_of_reencrypt_ne`) and a deliberate domain-separated variant of
implicit-rejection `FO-notbot` (§3.2.2, Fig. 12; `ImplicitSK`, `Scheme.keyGenNotBot`,
`Scheme.encapsNotBot`, `Scheme.decapsNotBot`, `decapsNotBot_encT_eq`,
`decapsNotBot_of_reencrypt_ne`) that tags `H : Bool × M × CT → K` with `false` for valid key
derivations and `true` for fallback rejection keys `H(true, dk.fallback, c)` in place of HHK17's
untagged `H(s, c)`. `FujisakiOkamoto.decTM`, `Scheme.decapsBotM` and `Scheme.decapsNotBotM` are
the same algorithms with oracle access to `G` and `H` in any monad. `decT`, `decapsBot` and
`decapsNotBot` are these in `Id` (`decT_eq`, `Scheme.decapsBot_eq` and `Scheme.decapsNotBot_eq`
give their direct forms), and with pure oracles in any lawful monad the oracle-access
decapsulations return them (`Scheme.decapsBotM_pure`, `Scheme.decapsNotBotM_pure`). The
random-oracle game handlers run them against lazy or table
oracles instead of restating the re-encryption check. For Random Oracle Model (ROM) IND-CCA games
and the keyless IND-CPA reduction
on `FO-notbot`, import
[`FujisakiOkamoto/Security.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Security.lean).
It defines the ROM query family `ROQuery M CT` (`G`, `H`, and punctured decapsulation rejecting
`c = cStar` with `none`) and its dispatcher `ROQuery.dispatch`, on which every lazy, eager and
simulated FO handler is built from its own `G`, `H` and decapsulation implementations (build new
hybrid handlers the same way), deterministic oracle adversaries `ROAdversary` on the challenge
record `KEM.Challenge PK CT K` (fields `pk`, `ct`, `key`; defined in
[`Encryption/KEM.lean`](../../CslibFrontier/Crypto/Computational/Encryption/KEM.lean)), pathwise
`(qG, qH)` query budgets `ROQueryBounds` via `OracleComp.IsCostBounded`, adversaries with explicit
coins `RandomizedROAdversary` (a coin draw `coins`, then the deterministic adversary `run ω`;
`ofDeterministic` for a single coin value; budgets `QueryBounds` and `FullQueryBounds` for every
coin value), and the lazy-cached executable game `Scheme.roIndCcaGame` (played by a randomized
adversary through `RandomizedROAdversary.play` in `Scheme.indCcaRomAdvantage`) and eager random-oracle game `Scheme.eagerIndCcaGame` with exact
eager/lazy equivalence (`Scheme.eval_roIndCcaGame_eq_eagerIndCcaGame`,
`Scheme.indCcaRomAdvantage_eq_eager`). Both games are instances of one ROM IND-CCA experiment
`Scheme.romIndCcaExperiment`, which takes the key generator and the decapsulation oracle as a
program `romProgram` against the random oracles `ROSpec`; its eager form is
`Scheme.eagerRomIndCcaExperiment`, and `Scheme.eval_romIndCcaExperiment_eq_eager` proves their
equivalence once for every decapsulation program. The `@[simp]` bridges
`Scheme.romIndCcaExperiment_notBot` and `Scheme.eagerRomIndCcaExperiment_notBot` (and
`Scheme.romIndCcaExperiment_bot`, `Scheme.eagerRomIndCcaExperiment_bot` for `FO^⊥` in `Bot.lean`)
identify the instances with the named games. For another FO variant, instantiate the experiment
with its decapsulation program and prove such bridges rather than writing new handlers and a new
eager/lazy proof. Eager games draw their random oracles from the named tables `Scheme.coinTable`
(for `G`) and `Scheme.keyTable X` (a key-valued table on `X`, such as `H` on `Bool × M × CT` or a
ciphertext table on `CT`); new eager hybrids should use them rather than spelling out `PMF.pi`.
The module also supplies the keyless simulator `Scheme.simHandler`, its run on a challenge
`Scheme.simFilterHit`, and the IND-CPA reduction `Scheme.romCpaReduction A`, one `TwoStage`
adversary whose first stage draws both challenge messages with `S.sampleMsg` (as `D₁` of HHK17
Fig. 8 does) and whose second stage runs `A` against the simulator and reports whether `m₁` was
queried to `G`. The one-wayness experiment of the challenge hop is `Scheme.simFilterOwExperiment`;
`Scheme.succProbability_simFilterOwExperiment_le` bounds it by the reduction's `cpaAdvantage` plus
`(qG + qH) / |M|`, and `RandomizedROAdversary.advantage_play_le` averages per-coin bounds over the
adversary's coins. The concrete per-instance IND-CCA advantage bound is
[`FujisakiOkamoto/NotBot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NotBot.lean):
`Scheme.indCcaRomAdvantage_le` bounds `indCcaRomAdvantage A` for uniform messages, a `δ`-correct
PKE and `(qG, qH)` random-oracle queries for every coin value (decapsulation queries unbounded) by
`2 · cpaAdvantage (romCpaReduction A) + (2 qH + 2 (qG + qH)) / |M| + 2 (qG + qH + 1) δ`. As in
HHK17 (§1.1.2 table, p. 6; §3.3 table, p. 22), no `γ`-spreadness is assumed. This is a concrete bound for one fixed scheme: there is
no security parameter and no running-time bound on the reduction; the word-level asymptotic
theorem `WordPKE.INDCPA.romINDCCA` below consumes it (where `roIndCcaGame` draws both real `H` values and the independent ideal challenge key from the arbitrary sampler `S.sampleKey`, recovering the uniform-key experiment of HHK17 §2.2 Def. 2.4 / Fig. 4 when `S.sampleKey` is uniform). Its hybrids are fixed in
`NotBot/Hybrids.lean` (`Scheme.eagerFbGame`, `Scheme.eagerCoupledGame`, `Scheme.coupledGame`),
one file per hop: fallback-seed decoupling (`NotBot/Fallback.lean`), re-indexing the oracles so
that decapsulation reads a ciphertext table (`NotBot/Pushforward.lean`) and its lazy realization
(`NotBot/Lazy.lean`), and the challenge hop (`Scheme.advantage_coupledGame_le` in
`NotBot/Challenge.lean`). The challenge hop keeps the decryption test `Dec(sk, c) = some m` in the
key-derivation oracle, so no message other than `m*` reaches the challenge key, and removes the
test only inside the one-wayness run, with the `δ`-correctness bad event of
`NotBot/Correctness.lean`.

For the post-secret-seed-guessing salted CORR hop used toward HQC, import
[`FujisakiOkamoto/Salted/Correctness.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Salted/Correctness.lean).
Its source-shaped query family keeps one fused joint query returning both the KEM key and PKE
coins, an independent rejection channel, and punctured decapsulation. At a fixed public key,
target-prefix joint queries take their key from the ciphertext-indexed `LD` table; an off-target
query instead has an independent key indexed by its full `(prefix, message, salt)` input and does
not inspect or change `LD`. `QueryBounds` counts direct joint and decapsulation queries separately
as `(qRO, qD)`; rejection queries have zero CORR cost.
`Scheme.closeTo_run_realHandler_simHandler` gives the fixed-key output-law bound
`(qRO + qD) * keyPairMaxFailProb`, and
`Scheme.advantage_randomizedRealHandler_simHandler_le` averages it over key generation using
`ExplicitCoinPKE.DeltaCorrect` (Glabush–Hövelmanns–Stebila, Definition 1, printed p. 6). The checked client
[`SaltedFOCorrectness.lean`](../../CslibFrontierTests/Crypto/SaltedFOCorrectness.lean) supplies
tight nonzero correctness and `(1,0)`, `(0,1)`, and `(1,1)` query-bound witnesses. Its exact Bool
regression checks that an off-target query leaves `LD` unchanged and that its key agrees with a
subsequent target key with probability `1 / 2`. This is a classical-ROM probability hop only: it
does not model the pre-guessing HQC fallback oracle or prove the full HQC Theorem 6.4/KEM endpoint.

To see why the re-encryption check of `T` cannot be omitted in `FO-notbot`, import [`FujisakiOkamoto/NoCheck.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/NoCheck.lean): for any explicit-coin PKE `P` over `Fin n → Bool`, `leakyPKE P` appends an `Option (Fin n)` tag to ciphertexts while preserving two-stage `cpaAdvantage` (`leakyPKE_cpaAdvantage`), `DeltaCorrect` (`leakyPKE_deltaCorrect`), and `GammaSpread` (`leakyPKE_gammaSpread`) and making `Scheme.decapsNotBot` reject tagged ciphertexts `(c, some i)` via the re-encryption check (`decapsNotBot_leakyPKE_some`), whereas dropping the re-encryption check (`Scheme.decapsNoCheck`, `Scheme.eagerNoCheckGame`) lets the bit-recovery adversary `leakAdv` (`roQueryBounds_leakAdv`, `0` `G`-queries and `n + 1` `H`-queries) achieve advantage at least `1 - (n + 1) / |K|` for a perfectly correct `P` and uniform keys (`advantage_eagerNoCheckGame_leakAdv`; checked client in [`CslibFrontierTests/Crypto/FujisakiOkamotoNoCheck.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoNoCheck.lean)). For explicit-rejection `FO^⊥ = U^⊥ ∘ T` (§3.2.1, Fig. 9), import [`FujisakiOkamoto/Bot.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Bot.lean) (`ROFullQueryBounds`, `Scheme.roIndCcaBotGame`, `Scheme.eagerIndCcaBotGame`, `Scheme.eval_roIndCcaBotGame_eq_eagerIndCcaBotGame`, `Scheme.simBotGame`, `Scheme.romBotCpaReduction`, `Scheme.indCcaBotAdvantage_le`, which removes the `2 qH / |M|` fallback seed-guessing term and adds the spreadness term `2 (qG + qH + qD) 2^{-γ}`, including the ciphertext-validity term over `qD` decapsulation queries, with `roIndCcaBotGame` and `eagerIndCcaBotGame` likewise drawing both real `H` replies and the independent ideal challenge key from `S.sampleKey` so uniform `S.sampleKey` recovers the standard uniform-ideal-key experiment) and [`FujisakiOkamoto/SpreadNecessity.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/SpreadNecessity.lean) (`unspreadPointPKE`, `unspreadScheme`, `probeDecapsAdv`, `advantage_eagerIndCcaBotGame_simBotGame_probeDecapsAdv`, showing that a single decapsulation query `qD = 1` with `qG = qH = 0` achieves distinguishing advantage `1 - 1 / |M|` against `simBotGame` when `γ`-spreadness fails at one message); standalone OW-PCA / OW-PCVA security definitions for `T` are not formalized separately. Checked clients in
[`CslibFrontierTests/Crypto/FujisakiOkamoto.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamoto.lean)
exercise honest `T`/`FO^⊥`/`FO-notbot` recovery and non-canonical-coin rejection on
`maskedShiftPKE`, zero-error and non-zero tight/non-tight `DeltaCorrect` witnesses (`noisyCoinPKE`
with failure probability `1 / 2`), positive and negative `GammaSpread` witnesses and fixed-message and two-stage IND-CPA
witnesses on `identityPKE`, and `ROQueryBounds`, `simFilterHit`, the exact two-stage advantage
`3 / 4` of `romCpaReduction`, positive `indCcaRomAdvantage`, and eager/lazy and one-wayness
witnesses on `identityScheme`, `identityUnifKeyScheme`, and `maskedShiftScheme`;
[`CslibFrontierTests/Crypto/FujisakiOkamotoNotBot.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoNotBot.lean)
and [`CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean`](../../CslibFrontierTests/Crypto/FujisakiOkamotoBot.lean)
instantiate `Scheme.indCcaRomAdvantage_le` (`≤ 1 / 4`) and `Scheme.indCcaBotAdvantage_le` (`≤ 1 / 4`, plus the `15 / 16` `probeDecapsAdv` separation on `unspreadPointPKE pairCoinPKE 0`) on `pairCoinScheme`.

For a security-parameter family over words, import
[`FujisakiOkamoto/Word.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/Word.lean).
`WordPKE` fixes at each parameter `n` the message length, the coin length and a bound on ciphertext
lengths, and `WordPKE.IsEfficient` asks for strict PPT key generation and polynomial-time
encryption and decryption. `WordPKE.CiphertextFits` says that encryption under generated keys
stays within the ciphertext bound, and `WordPKE.INDCPA` is IND-CPA security of `WordPKE.encrypt`
with challenge messages of length `msgLen n`. `WordPKE.scheme P keyLen n` is the `Scheme` bundle
at `n`, and the native algorithms query word oracles `G` and `H` (`RO`): `WordPKE.keyGenNotBot`,
`WordPKE.encaps`, and `WordPKE.decapsNotBot` and `WordPKE.decapsBot`, which reject words longer
than the ciphertext bound and otherwise run `Scheme.decapsNotBotM` and `Scheme.decapsBotM`. Their
native certificates (`WordPKE.IsEfficient.isPPTOn_keyGenNotBot`,
`WordPKE.IsEfficient.isOraclePPTOn_encaps`, `WordPKE.IsEfficient.isOraclePPTOn_decapsNotBot`,
`WordPKE.IsEfficient.isOraclePPTOn_decapsBot`) follow from `IsEfficient`.
[`FujisakiOkamoto/WordReduction.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/WordReduction.lean)
gives the IND-CPA reduction for this family as an `Encryption.AdversaryOf`
(`WordPKE.romFilterCpaReductionWord`, and `WordPKE.romCpaReductionWord` for `FO-notbot`). It wraps a
word adversary `A : ℕ → List Bool → WordOracleComp CCAOp Bool` with oracles `G`, `H` and
decapsulation. Its native keyless simulator `WordPKE.simFilterWordHandler` answers requests in the
domain with the typed `Scheme.simFilterHandler` of the bundle, and answers any other request with
the empty word without changing its state. `WordPKE.IsEfficient.isPPT_romCpaReductionWord` proves
the reduction uniform strict PPT from `IsOraclePPT encBool A`, covering the lazy `G`/`H`
simulation. The security notion is in
[`FujisakiOkamoto/WordGame.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/WordGame.lean):
`WordPKE.romIndCcaGameWord` is the IND-CCA game of HHK17 Def. 2.4 / Fig. 4 with lazily sampled
random oracles `G` and `H` (`WordPKE.roWordOracle`), the native encapsulation for the challenge,
and the native decapsulation for the decapsulation oracle (`WordPKE.ccaWordOracle`).
`WordPKE.ROMINDCCA` asks for negligible advantage against every `IsOraclePPT` adversary.
[`FujisakiOkamoto/WordBridge.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/WordBridge.lean)
relates these word objects to the typed ones at each parameter. `WordPKE.finiteScheme P keyLen n` is
the bundle over bit strings and the ciphertext space `WordPKE.Ciphertext P n`, and
`WordPKE.DeltaCorrect` is the correctness of the family, stated for that bundle. `WordPKE.IsEfficient.exists_typedAdversary` turns each `IsOraclePPT`
adversary into a typed adversary at each parameter (`WordPKE.savedCoinAdversary`, a replay of its
saved coins) with polynomially many `G` and `H` queries; when the ciphertexts fit, the word game is
its typed `Scheme.roIndCcaGame`, and the advantage of `romCpaReductionWord` is the typed
`cpaAdvantage` of `Scheme.romCpaReduction`.
[`FujisakiOkamoto/WordSecurity.lean`](../../CslibFrontier/Crypto/Protocols/KEM/FujisakiOkamoto/WordSecurity.lean)
proves the asymptotic theorem `WordPKE.INDCPA.romINDCCA`: IND-CPA security of an efficient family
whose ciphertexts fit, which is `δ`-correct with `δ` and `2^{-msgLen}` negligible, implies
`ROMINDCCA`. As in HHK17, no `γ`-spreadness is assumed. Its proof applies `INDCPA` to
`romCpaReductionWord A` through `isPPT_romCpaReductionWord` and bounds the rest with the concrete
per-instance bound `Scheme.indCcaRomAdvantage_le`. `FO^⊥` has no word-level theorem yet.

ML-KEM ([fips203][fips203]) lives in
[`MLKEM/KPKE.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/KPKE.lean),
[`MLKEM/Security.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Security.lean) and
[`KEM/MLKEM.lean`](../../CslibFrontier/Crypto/Protocols/KEM/MLKEM.lean). K-PKE reuses
`ModuleLWEPublicKey`, `moduleSISMap` and `innerPoly`: its uncompressed ciphertext is
`moduleLWEEncrypt` of the zero message shifted by `messagePoly`, since FIPS 203 encodes the bit `1`
as `⌈q / 2⌋` rather than `encodePolyMsg`'s `⌊q / 2⌋`. The FIPS 203 rounding maps `compress` and
`decompress` come with `compress_decompress`, the rounding-error bound
`natAbs_valMinAbs_decompress_compress_sub_le` and one-bit decoding
`compress_one_decompress_one_add`, which together give the deterministic bounded-noise correctness
`decrypt_encrypt_eq_of_noise_le`. Key generation and coins are `ProbComp` programs over
`sampleCenteredBinomial` with a uniform matrix in place of `SampleNTT`, and `toExplicitCoinPKE`
feeds the scheme to the FO layer. `cpaAdvantage_le` bounds its two-stage IND-CPA advantage
(`ExplicitCoinPKE.cpaAdvantage`, messages chosen by the adversary after seeing the public key) by
four `ModuleLWE.advantage` terms: the public-key hop `mlweKeyReduction A b` and the ciphertext hop
`mlweReduction A b` for each challenge bit `b`, with centered-binomial secret and error laws. Both
reductions are explicit programs that run the adversary's first stage themselves, as in the hops of
Kyber v3.02 ([kyber302][kyber302], §4.4, eq. (6)), with a uniform matrix in the public key in
place of the seed `ρ` and `XOF`, no random oracles, and a ciphertext hop on the uncompressed sample.
The bound is concrete and charges no running time.
[`MLKEM/Native.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Native.lean) gives K-PKE
on residue lists, with `SamplePolyCBD` from fair bits (`uniformList_map_cbdResidues`) and native
encryption and decryption proved to compute `encrypt` and `decrypt`, and
[`MLKEM/Family.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Family.lean) packages them
as the word-level family `kpke P : WordPKE` for a parameter family `P`, efficient when `P` is
computable in polynomial time (`kpke_isEfficient`) and with ciphertexts that fit
(`kpke_ciphertextFits`). Its key generation draws the matrix coefficientwise at precision `κ`,
within `k * k * n / 2 ^ κ` of uniform (`closeTo_keyGenWord`).
[`MLKEM/Asymptotic.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Asymptotic.lean)
proves `indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`, IND-CPA of K-PKE with ideal coin
expansion and the matrix in the public key. It is a step towards Kyber v3.02 Theorem 1
([kyber302][kyber302], §4.3.1), not that theorem, for two reasons. Key generation and encryption
draw their centered-binomial noise from fair coins, where Kyber v3.02 and FIPS 203 expand a seed
with `PRF`, so the bound has no `Adv^prf` term. And the public key carries the sampled matrix in
place of the seed `ρ` from which Kyber's encryption re-derives it with `XOF`, while the adversary
has no `XOF` or `G` oracle: Theorem 1 assumes that both are random oracles, and the step that
answers the adversary's `XOF` queries at `ρ` with the Module-LWE matrix is not formalized. The
`PRF` hop and this random-oracle lift are open under
[#5293](https://github.com/cslib-community/cslib-frontier/issues/5293#issuecomment-6893099765).
The theorem shows that `kpke P` is IND-CPA secure under `DecisionModuleLWEWith` with the
centered-binomial laws `cbdLaw`: width `η₁` for both laws at the `k × k` key shape, and `η₁`
secrets with `η₂` errors at the `(k + 1) × k` ciphertext shape. It applies the assumption to the
hops as families `keyReduction` and `ciphertextReduction` through `isPPT_keyReduction` and
`isPPT_ciphertextReduction`, proved from the adversary's certificate, and bounds the rest with
`cpaAdvantage_le` and the matrix sampler's distance. Its other deviation is the uncompressed
ciphertext hop of `cpaAdvantage_le` above, and it is not a statement about ML-KEM.
`MLKEMTransform.decapsWith` is the FIPS 203 implicit-rejection wrapper over any
`ExplicitCoinPKE`, defined through `FujisakiOkamoto.decT` and proved equal to the standard's
decapsulation algorithm (`decapsWith_eq`). [`CslibFrontierTests/Crypto/MLKEM.lean`](../../CslibFrontierTests/Crypto/MLKEM.lean)
checks the three parameter sets, sharpness of the compression and decoding bounds at `q = 3329`,
and a toy instance (`n = 2`, `q = 17`) on which the noise hypotheses hold, decryption and
decapsulation succeed, and a tampered ciphertext is implicitly rejected.

The independent source boundary in
[`MLKEM/Encoding.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/Encoding.lean) gives
Algorithms 5–6 their exact 256-coefficient, `32 * d`-byte types. It packs fields and bytes least
significant bit first through the shared `BitString.packWords`/`readPackedField` API, proves every
coefficient vector round-trips, and exposes Section 7.2's decode/re-encode canonicality check; at
width 12, raw values `3329 ... 4095` reduce modulo 3329 and are therefore noncanonical. The
[`SeedExpansion.lean`](../../CslibFrontier/Crypto/Computational/SIS/MLKEM/SeedExpansion.lean)
boundary fixes Algorithm 13's `rho || j || i` order, the 33-byte SHAKE256 PRF input and its
128-/192-byte outputs, and Algorithm 7's three-byte nibble parser. Its finite-prefix parser does
not claim that a bounded SHAKE128 prefix always supplies 256 accepted values. The
[ordinary-import clients](../../CslibFrontierTests/Crypto/MLKEMEncoding.lean) include cross-byte
round trips, the canonical coefficient 3328, the rejected raw word 3329, nibble-order cases and
the column-before-row suffix. This layer does not serialize the complete K-PKE/KEM, identify the
NTT representation with coefficient form, prove seed-derived uniformity or security, or claim
constant-time execution or FIPS validation.

For multi-block symmetric modes of operation over `BitString n`, import
[`BlockCipher/Modes.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/Modes.lean)
(Katz–Lindell 3rd ed., §3.6.2–§3.6.4 and Exercises 3.21, 3.24, 3.25, 3.29, 3.30, 3.32, 3.33).
It defines CBC (`cbcEncryptBlocks`, `cbcDecryptBlocks`), OFB (`ofbChain`, `ofbEncryptBlocks`,
`ofbDecryptBlocks`), counter mode (`ctrMaskBlocks`, `ctrEncryptBlocks`, `ctrDecryptBlocks`), and
self-synchronizing CFB (`cfbEncryptBlocks`, `cfbDecryptBlocks`, included alongside KL's modes) with
round-trip inversion theorems and the identity `ofbChain_eq_cbcEncryptBlocks_replicate_zero`
equating the OFB keystream chain with CBC encryption of all-zero plaintext blocks. The generic
sampling facts live in
[`Probability/BitString/Collision.lean`](../../CslibFrontier/Probability/BitString/Collision.lean):
under an ideal random function `PMF.uniformOfFintype (BitString n → BitString n)`,
`BitString.map_evalPoints_uniformOfFintype` and `BitString.map_xorEvalPoints_uniformOfFintype` give
keystream and ciphertext uniformity on fixed (non-adaptive) injective point schedules (such as CTR
counters), and `BitString.toOuterMeasure_addRight_mem_finset_eq` and
`BitString.toOuterMeasure_addRight_mem_list_le` give the shifted-block collision probabilities
`S.card / 2^n` and at most `ks.length / 2^n`. The modes module builds on them with
`advantage_xorEvalPoints_eq_zero`, the uniform-block XOR and support-length helpers
(`uniformBlocks_eq`, `length_snd_of_mem_support_uniformDraws`, `map_zipWith_uniformBlocks`,
`map_iv_uniformBlocks_zipWith`), and the chain collision bound `toOuterMeasure_badChain_le`
(`bs.length * (ks.length + bs.length) / 2^n`, over `uniformBlocks`, the `PMF.iid` uniform blocks read
as a list) used when analyzing random-IV chaining. The indexed OFB and CTR masks decrypt the
list-mode ciphertexts (`maskBlockDecrypt_ofbBlockMask_ofbEncryptBlocks`,
`maskBlockDecrypt_ctrBlockMask_ctrEncryptBlocks`); indexed block `j ≥ 1` of `ctrBlockMask` uses
counter value `j - 1`, matching list block `j - 1` of `ctrMaskBlocks`. The module
also proves mode separations and counterexamples for same-IV reuse (`advantage_streamIVReuseGame_eq`,
`cfbSameIVRecover_cfbEncryptBlocks`), overlapping counter/stream nonces
(`ctrEncryptBlocks_overlapping_nonce`, `advantage_overlappingStreamGame_eq`), predictable-IV CBC
chosen-plaintext attacks (`advantage_cbcPredictableIVGame_eq_one`), linear XOR and modular/group
additive-IV modes (`xorFunctionCipherRecover_correct`, `additiveModeDistinguisher_spec`), and
single-bit/dropped-block error-propagation laws (`maskBlockDecrypt_flipBit`,
`cbcBlockDecrypt_flipBit`, `cfbBlockDecrypt_flipBit`, `cbcBlockDecrypt_dropBlock`,
`cfbBlockDecrypt_dropBlock`, `maskBlockDecrypt_dropBlock`). Concrete `BitString 4` and
`ZMod (2 ^ 4)` checks, including indexed CTR decryption of list CTR ciphertexts under a
nonconstant counter schedule, are in
[`CslibFrontierTests/Crypto/BlockCipherModes.lean`](../../CslibFrontierTests/Crypto/BlockCipherModes.lean),
and direct checks of the sampling lemmas are in
[`CslibFrontierTests/BitStringCollision.lean`](../../CslibFrontierTests/BitStringCollision.lean).

For the shared lazy-versus-fresh random-function hybrid and left-or-right block-mode CPA scaffolding
used by both CTR and OFB mode, import
[`Encryption/RandomFunctionHybrid.lean`](../../CslibFrontier/Crypto/Computational/Encryption/RandomFunctionHybrid.lean):
it packages `FlagState`, the caching/fresh step handlers `lazyStep` and `freshStep`, the game
equivalence `idealExperiment_eq_runWith_lazyStep`, the bad-flag reduction bounds
`advantage_lazy_fresh_le` and `advantage_idealExperiment_freshStep_le` (whose lifted-coin support
facts `PMF.snd_eq_of_mem_support_lift` and `PMF.toOuterMeasure_lift_eq_zero` live in
[`Probability/PMF/Support.lean`](../../CslibFrontier/Probability/PMF/Support.lean)), the two- and
four-hop advantage triangle helpers `advantage_le_two` and `advantage_le_four`, and the shared
block-mode query, cost, oracle, reduction, and ideal-experiment interface (`BlockModeQuery`,
`BlockModeSpec`, `BlockModeAdversary`, `blockModeSelect`, `blockModeBlocks`, `blockModeCost`,
`blockModeOracle`, `blockModeIdealOracle`, `blockModeCpaExperiment`, `blockModeIdealExperiment`,
`blockModeQueryProgram`, `blockModeReduction`, `blockModeCpaExperiment_eq_realExperiment`,
`isQueryBounded_blockModeReduction`, and `freshGame_eq_blockModeIdealExperiment`). The two
experiments are `ProbComp Bool` runs of the adversary (`adversary.run`), and the reduction is
`ProbOracleComp.simulate (blockModeQueryProgram keystream ℓ b) adversary`, so its query bound is
`isCostBounded_simulate` and the CPA experiment equals `PRF.realExperiment` before evaluation.

For the chosen-plaintext security of random-IV counter (CTR) mode, import
[`Encryption/CTRMode.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CTRMode.lean)
(Katz–Lindell 3rd ed., §3.6.3, Figure 3.9, Definition 3.22, Theorem 3.33 [katzlindell20][katzlindell20];
Boneh–Shoup Chapter 4 [bs23][bs23]). Using the shared `BlockModeAdversary` / `blockModeCost` /
`blockModeIdealExperiment` interface, it formalizes the adaptive left-or-right multiple-encryption
experiment (`ctrCpaGame`) for any counter schedule `counter : BitString n → ℕ → BitString n`
satisfying within-query offset distinctness and per-offset IV injectivity, proves exact real-PRF
correspondence for `ctrReduction` (`ctrCpaGame_eq_realExperiment`, `isQueryBounded_ctrReduction`), bounds
the idealization collision error relative to `blockModeIdealExperiment` by `K ^ 2 / 2 ^ n` for `K` total
queried blocks (`advantage_idealExperiment_ctrReduction_le`), and specializes to the modular-addition
counter `ctrModCounter` whenever per-query length `ℓ ≤ 2 ^ n` (`ctrModCounter_injOn`,
`ctrModCounter_injective_left`, `advantage_ctrCpaGame_ctrModCounter_randomFunction_le`,
`advantage_ctrCpaGame_ctrModCounter_le`). These typed reductions carry no efficiency certificate.
Concrete `BitString 8` evaluations and non-vacuous bounds are in
[`CslibFrontierTests/Crypto/CTRMode.lean`](../../CslibFrontierTests/Crypto/CTRMode.lean).

The uniform statement is in
[`Encryption/CTRMode/Uniform.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CTRMode/Uniform.lean)
(Boneh–Shoup v0.6, §5.4.2 and Theorem 5.3 [bs23][bs23]). `ctrWordEncrypt` is randomized counter
mode with `n`-bit blocks at parameter `n` for a word-level family, an instance of the random-IV
stream envelope `ivStreamEncrypt`
([`Encryption/IVStream.lean`](../../CslibFrontier/Crypto/Computational/Encryption/IVStream.lean)),
with certified honest algorithms
(`isPPTOn_ctrWordEncrypt`, `computableInPolyTime_ctrWordDecrypt`) and correctness
(`ctrWordDecrypt_ctrWordEncrypt`). The reduction `ctrToPrfDistinguisher` is the shared random-IV
stream reduction `ivStreamToPrfDistinguisher`
([`Encryption/IVStream/Reduction.lean`](../../CslibFrontier/Crypto/Computational/Encryption/IVStream/Reduction.lean))
with one PRF query per counter block. Its certificate `isOraclePPT_ctrToPrfDistinguisher` and its
real- and ideal-game identities are instances of the shared ones
(`isOraclePPT_ivStreamToPrfDistinguisher`, `eval_prfRealGame_ivStreamToPrfDistinguisher`,
`eval_prfIdealGame_ivStreamToPrfDistinguisher`).
`advantage_ctrWordCPAGame_le` reuses the typed collision bound above, and
`PseudorandomFunction.indcpa_ctrWordEncrypt` proves `SymmetricINDCPAOn blockPairValid` from
`PseudorandomFunction family` alone. `SymmetricINDCPAOn`
([`Encryption/SymmetricCPA.lean`](../../CslibFrontier/Crypto/Computational/Encryption/SymmetricCPA.lean))
is the many-query left-or-right game of Attack Game 5.2 with a challenge-pair predicate;
`SymmetricCipher.INDCPA` is its `n`-bit case (`SymmetricCipher.indcpa_iff`). Examples are in
[`CslibFrontierTests/Crypto/CTRModeUniform.lean`](../../CslibFrontierTests/Crypto/CTRModeUniform.lean).

For the chosen-plaintext security of random-IV OFB mode, import
[`Encryption/OFBMode.lean`](../../CslibFrontier/Crypto/Computational/Encryption/OFBMode.lean)
(Katz–Lindell 3rd ed., §3.6.3, Figure 3.8, Definition 3.22, following the proof of Theorem 3.33
[katzlindell20][katzlindell20]). `ofbCpaGame` is the left-or-right multiple-encryption experiment
for a keyed block function using `BlockModeAdversary`, `blockModeSelect`, and `blockModeBlocks`,
where a pair whose lengths differ or exceed `ℓ` blocks encrypts the empty message. `ofbReduction`
turns an adversary into a PRF distinguisher that computes the keystream with its oracle
(`ofbCpaGame_eq_realExperiment`, `isQueryBounded_ofbReduction`). If the queries ask at most `K` blocks in
total (`OracleComp.IsCostBounded (blockModeCost ℓ) adversary K`), `advantage_idealExperiment_ofbReduction_le`
bounds the distance from `blockModeIdealExperiment` by `K * (K + ℓ) / 2^n` using
`toOuterMeasure_badChain_le`. `advantage_ofbCpaGame_le` then bounds the left-or-right advantage by
the two PRF advantages plus `2 * K * (K + ℓ) / 2^n`, and
`advantage_ofbCpaGame_randomFunction_le` gives `2 * K * (K + ℓ) / 2^n` for a uniform random
function. These typed reductions carry no efficiency certificate. Concrete checks are in
[`CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean`](../../CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean).

The uniform statement is in
[`Encryption/OFBMode/Uniform.lean`](../../CslibFrontier/Crypto/Computational/Encryption/OFBMode/Uniform.lean)
(Boneh–Shoup v0.6, Exercise 5.15(b) [bs23][bs23]), parallel to the CTR one. `ofbWordEncrypt` is
OFB mode with `n`-bit blocks for a word-level family, with each chain value truncated to `n` bits
so that encryption is polynomial-time on every key (`isPPTOn_ofbWordEncrypt`,
`computableInPolyTime_ofbWordDecrypt`, `ofbWordDecrypt_ofbWordEncrypt`). The reduction
`ofbToPrfDistinguisher` is the shared stream reduction `ivStreamToPrfDistinguisher` of the CTR
paragraph, querying its oracle on each chain value. Its certificate
`isOraclePPT_ofbToPrfDistinguisher` and its real- and ideal-game identities are instances of the
shared ones. Through `blockModeWordAdversary`
([`Encryption/BlockModeWord.lean`](../../CslibFrontier/Crypto/Computational/Encryption/BlockModeWord.lean))
it matches `ofbReduction`, so `advantage_ofbWordCPAGame_le` reuses the chain bound above, and
`PseudorandomFunction.indcpa_ofbWordEncrypt` proves `SymmetricINDCPAOn blockPairValid` from
`PseudorandomFunction family` alone. Examples are in
[`CslibFrontierTests/Crypto/OFBModeUniform.lean`](../../CslibFrontierTests/Crypto/OFBModeUniform.lean).

For hash functions built from a fixed permutation or block cipher, import
[`Hash/Sponge.lean`](../../CslibFrontier/Crypto/Primitives/Hash/Sponge.lean) and
[`Hash/BlockCipherCompression.lean`](../../CslibFrontier/Crypto/Primitives/Hash/BlockCipherCompression.lean)
(Katz–Lindell 3rd ed., §7.3.1 and §7.3.3). The sponge module writes the state as a pair
`(rate, capacity)` with an arbitrary output map and defines `absorb`, `squeeze`, `pad`, `toBlocks`
and `hash` (Construction 7.6). `badEvent_of_hash_eq` is the deterministic core of Claim 7.8 for
forward permutation queries: a collision between distinct messages triggers `ImageCollision` for
the output map (E1), `ZeroCapacity` (E2) or `ImageCollision` for `Prod.snd` (E3) among the
evaluated inputs. `hash_eq_of_capacity_eq` extends any capacity collision to a hash collision, and
`hash_prodCongr_collision` answers Exercise 7.26. Inverse queries, Claim 7.9 and the bound of
Theorem 7.7 are not formalized. The block-cipher module defines Davies–Meyer (`daviesMeyer`) and
the compression functions of Exercise 7.23(a) and (c) (`cipherOutput`, `keyMasked`), with
inverse-query collisions (`cipherOutput_collision`, `keyMasked_collision`) and the fixed-point
collision of Exercise 7.24 (`daviesMeyer_collision_of_fixedPoints`); the Ideal-Cipher bound of
Theorem 7.5 is proved in `daviesMeyer_collisionGame_le` and `daviesMeyer_collisionGame_mul_le`
(combining `daviesMeyer_collision_difference_bound` with the forgetful collision bound) in
[`CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean`](../../CslibFrontier/Crypto/Primitives/IdealCipher/Compression.lean). Concrete checks are in
[`CslibFrontierTests/Crypto/Sponge.lean`](../../CslibFrontierTests/Crypto/Sponge.lean) and
[`CslibFrontierTests/Crypto/IdealCipherCompression.lean`](../../CslibFrontierTests/Crypto/IdealCipherCompression.lean).

For the single-oracle real-versus-ideal formulation of authenticated encryption ([katzlindell20][katzlindell20], §5.2, Definition 5.4 and Theorem 5.5, pp. 152–153), import [`Encryption/RealIdealAE.lean`](../../CslibFrontier/Crypto/Computational/Encryption/RealIdealAE.lean). `SymmetricCipher.aeRealGame` answers `n`-bit encryption queries honestly (recording returned ciphertexts and answering decryption queries on them with `[]`) and decrypts fresh ciphertexts via `encOption encBits (E.decrypt n k ct)`, whereas `aeIdealGame` encrypts `List.replicate n false` and answers every decryption query with `[]`; `RealIdealAE` asks every `IsOraclePPT encBool` adversary to have negligible advantage, and `realIdealAE_iff_indcca_and_ciphertextIntegrity` and `realIdealAE_iff_authenticatedEncryption` prove equivalence with `INDCCA ∧ CiphertextIntegrity` and `AuthenticatedEncryption` via `cpaToAEAdversary`, `ciToAEAdversary`, and `aeToCCAAdversary`. [`Encryption/HalfBlockPRP.lean`](../../CslibFrontier/Crypto/Computational/Encryption/HalfBlockPRP.lean) formalizes the half-block construction `BlockCipher.halfBlockCipher` (`F_k(r ‖ m)` on `2 n`-bit blocks, Exercises 5.8 and 5.9, p. 165) and shows via the zero-query `allOnesForger` that it fails `CiphertextIntegrity`, `AuthenticatedEncryption`, and `RealIdealAE` for every block cipher (its CCA security under a strong PRP is not formalized); checked instances over an identity cipher are in [`CslibFrontierTests/Crypto/RealIdealAEAndHalfBlock.lean`](../../CslibFrontierTests/Crypto/RealIdealAEAndHalfBlock.lean).

For fresh-message encryption unforgeability ([katzlindell20][katzlindell20], §5.2, Definition 5.2,
p. 151, and Exercise 5.5, p. 165), import
[`Encryption/EncForge.lean`](../../CslibFrontier/Crypto/Computational/Encryption/EncForge.lean).
`SymmetricCipher.encForgeGame` and `SymmetricCipher.EncForge` test whether a uniform strict
`IsOraclePPT encBits` adversary can produce a ciphertext decrypting to `some m` for a plaintext `m`
not queried to `encForgeOracle`. Ciphertext integrity implies `EncForge`
(`SymmetricCipher.succProbability_encForgeGame_le_ciGame`, `CiphertextIntegrity.encForge`), and
ordinary fresh-message MAC security (`MACScheme.EUFCMA`, without `SUFCMA` or `E.INDCPA`) already
suffices for `(encryptThenMAC E M hctLen).EncForge` (`succProbability_encForgeGame_encryptThenMAC_le`,
`encForge_encryptThenMAC`, Exercise 5.5). The generic authenticated-encryption composition
separations (Exercises 5.4 and 5.10, pp. 164–165) are in
[`Encryption/CompositionCounterexamples.lean`](../../CslibFrontier/Crypto/Computational/Encryption/CompositionCounterexamples.lean).
`SymmetricCipher.tailFallback` (falling back to `E.decrypt n k ct.tail` when direct decryption
returns `none` and `ct` is non-empty) preserves `INDCPA` and `EncForge` while breaking
`OneTimeCiphertextIntegrity`, `CiphertextIntegrity`, `OneTimeINDCCA`, and `INDCCA`
(`SymmetricCipher.tailFallback_counterexample`,
`PseudorandomFunction.tailFallback_prfEncryptThenMAC_counterexample`, Exercise 5.10); and
`MACScheme.redundantTag` (accepting `tag` or `tag.tail`) preserves `EUFCMA` while breaking `SUFCMA`,
so `encryptThenMAC E M.redundantTag hctLen` satisfies `INDCPA` and `EncForge` yet fails
`CiphertextIntegrity` and `INDCCA` with advantage `1` for every `n ≥ 1`
(`encryptThenMAC_redundantTag_counterexample`,
`PseudorandomFunction.prfEncryptThenMACRedundantTag_counterexample`, Exercise 5.4). Concrete
evaluations and composed `IsPPT` / `IsOraclePPT` checks on `echoFamily` are in
[`CslibFrontierTests/Crypto/CompositionCounterexamples.lean`](../../CslibFrontierTests/Crypto/CompositionCounterexamples.lean).

For generic MAC-then-Encrypt composition, its `INDCPA` preservation, and its chosen-ciphertext
counterexample over `SymmetricCipher` and `MACScheme`, import
[`Encryption/MACThenEncrypt.lean`](../../CslibFrontier/Crypto/Computational/Encryption/MACThenEncrypt.lean)
(Katz–Lindell 3rd ed., §5.2 [katzlindell20][katzlindell20]; Boneh–Shoup §9.4.1 [bs23][bs23]).
Given a polynomial-time plaintext-tag length schedule `ptLen : ℕ → ℕ`
(`hptLenPoly : ComputableInPolyTime ptLen encUnary encUnary`), `M.msgLen n = n`, and
`(encPair encBits encBits (msg, tag)).length = ptLen n` on valid `M` messages and tags,
`macThenEncrypt E M ptLen hptLenPoly hmsgLen hpairLen` signs `msg` and runs `E` at security
parameter `ptLen n` on `encPair encBits encBits (msg, tag)` (requiring no extra decryption
hypothesis beyond `E.decrypt_encrypt`), verifying length, framing round-trip, and `M.verify` on
decryption. When `StrictMono ptLen`, `indcpa_macThenEncrypt` reduces `INDCPA` of `macThenEncrypt`
to `E.INDCPA` via `mteToCPAAdversary` (reindexing `ptLen` with `GeneratorReindex`). The malleable
wrapper `SymmetricCipher.extendCipher` appends `false` to every ciphertext and ignores the last bit
in decryption, preserving `INDCPA` (`SymmetricCipher.INDCPA.extendCipher`) and `OneTimeINDCPA`
(`SymmetricCipher.OneTimeINDCPA.extendCipher`) via `extendCPAAdversary` and
`extendOneTimeCPAAdversary`. Meanwhile, flipping that trailing bit (`macThenEncryptExtendCIAdversary`,
`macThenEncryptExtendCCAAdversary`) achieves advantage `1` for every `n ≥ 1` against
`macThenEncrypt E.extendCipher M ptLen ...`, refuting `OneTimeCiphertextIntegrity`,
`CiphertextIntegrity`, `OneTimeINDCCA` (`not_oneTimeINDCCA_macThenEncrypt_extendCipher`), and
`INDCCA` (`not_indcca_macThenEncrypt_extendCipher`), combined in
`macThenEncrypt_extendCipher_counterexample` and instantiated unconditionally from any
`PseudorandomFunction` via `prfMacThenEncryptExtend` (`ptLen n = 3 * n + 1`) and
`PseudorandomFunction.prfMacThenEncryptExtend_counterexample`. Concrete checks on `echoCipher` and
`echoMAC` as well as the PRF instantiation are in
[`CslibFrontierTests/Crypto/MACThenEncrypt.lean`](../../CslibFrontierTests/Crypto/MACThenEncrypt.lean).

## Authentication, signatures, and state

To state a forgery experiment, import [Game/Forgery.lean](../../CslibFrontier/Crypto/Game/Forgery.lean). `forgeExperiment keyGen signer verify fresh A` draws a key pair, runs the forger `A` on the public key against a signing oracle, and accepts a candidate `(m, σ)` that verifies and is fresh. The oracle is a policy `Signer SK M Sig` that reads the log of answered queries. `Signer.ofSign` signs every query and `.oneTime` signs only the first; `Signer.indexed` and `Signer.counter` give the indexed and counter oracles. A refused query is answered with `default` and is not logged. `freshMessage` gives existential unforgeability and `freshPair` strong unforgeability; `succProbability_forgeExperiment_freshMessage_le` shows that strong implies existential. Verification also receives the secret key, so a MAC is the case `PK = Unit`. [Signature/Scheme.lean](../../CslibFrontier/Crypto/Computational/Signature/Scheme.lean) defines a typed `Signature.Scheme PK SK M Sig` with `eufCmaExperiment` (Boneh–Shoup Attack Game 13.1), `sufCmaExperiment` and `oneTimeEufCmaExperiment`; `restrict adm` makes verification accept only admissible messages. At each parameter `n`, the word games `SignatureScheme.eufCmaGame` and `eufOneTimeGame` equal these experiments for `S.toScheme n` and `adversary.toTyped n` ([Signature/Bridge.lean](../../CslibFrontier/Crypto/Computational/Signature/Bridge.lean), `eufCmaGame_eq_eufCmaExperiment`). `Signature.IndexedScheme` adds a capacity and passes an index to signing and verification. Its `eufCmaExperiment` uses `Signer.indexed` (Boneh–Shoup Definition 14.6) and `counterEufCmaExperiment` uses `Signer.counter` (Section 14.6.4). The word games `indexedEufCmaGame` and `counterEufCmaGame` equal them at each `n` (`indexedEufCmaGame_eq_eufCmaExperiment`, `counterEufCmaGame_eq_counterEufCmaExperiment`). For any typed scheme on words, `Forger.eval_eufCmaExperiment_toTyped` and its `restrict` form unfold the experiment played by a word forger into the word-level game; the tree signature games `TreeSignature.treeGame` and `treeGameWith` are experiments of the certificate-free `treeScheme` and use this form in the coin hybrid. The [checked clients](../../CslibFrontierTests/Crypto/Forgery.lean) cover the signing policies, a winning forger, a replay that loses, and the unique-signature equality.

[SignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/Signature.lean#L87) bundles efficient key generation, signing, verification and correctness. The base message space is exactly `n` bits. Its oracle forger chooses signing requests adaptively; ordinary EUF-CMA rejects any message previously signed. [exists_oneWay_iff_exists_oneTimeSignature](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/OneWayToSignature.lean#L882) is the OWF/one-time-signature equivalence via Lamport's construction. Stateless many-time `EUFCMA` `SignatureScheme`s on `n`-bit messages are constructed from any `OneWayPermutation` in [`TCRSignature.lean`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) (`OneWayPermutation.exists_eufCMA`) and from any general `OneWay` function in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) (`OneWay.exists_eufCMA`, `exists_oneWay_iff_exists_signature`, `exists_oneTimeSignature_iff_exists_signature` [rompel90][rompel90]). For unrestricted bit-string messages (`msg : List Bool`), [`WordSignatureScheme`](../../CslibFrontier/Crypto/Computational/WordSignature.lean) removes the `n`-bit message-length filter from signing, verification and `eufCmaGame` (`WordSignatureScheme.EUFCMA`, strictly stronger than `toSignatureScheme.EUFCMA`). When full collision resistance is available, [`HashAndSign.scheme`](../../CslibFrontier/Crypto/Computational/HashAndSign.lean) (Katz–Lindell 3rd ed., §13.3, Construction 13.3 and Theorem 13.4, pp. 467–468 [katzlindell20][katzlindell20]) fixes a single hash key `s` once in the public and secret keys (`⟨pk₀, s⟩`, `⟨sk₀, s⟩`) so that signatures carry no per-signature hash-key overhead (`HashAndSign.succProbability_eufCmaGame_le`, `SignatureScheme.EUFCMA.wordEUFCMA_hashAndSign`, `SignatureScheme.EUFCMA.wordEUFCMA_of_hashFamily`, `SignatureScheme.EUFCMA.wordEUFCMA_merkleDamgard`, and key-independent collision attack `HashAndSign.not_eufCMA_scheme_of_collision`; concrete checks in [`CslibFrontierTests/Crypto/HashAndSign.lean`](../../CslibFrontierTests/Crypto/HashAndSign.lean)). Under only target collision resistance (UOWHFs), [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) lifts any `SignatureScheme.EUFCMA` scheme by sampling a fresh hash key per signature (`SignatureScheme.EUFCMA.eufCMA_wordScheme`, `OneWayPermutation.exists_wordEUFCMA`; Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23]), and [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) closes the unrestricted-message equivalence from any uniform `OneWay` function (`OneWay.exists_wordEUFCMA`, `exists_oneWay_iff_exists_wordSignature`, `exists_oneTimeSignature_iff_exists_wordSignature` [rompel90][rompel90]).

Reductions that truncate signing-oracle replies need a polynomial bound on signature length. Take it
from `SignatureScheme.exists_sign_length_bound` (in the parameter and the message length),
`SignatureScheme.exists_sign_length_bound_of_length_eq` (on `n`-bit messages) or
`IndexedSignatureScheme.exists_sign_length_bound` (at indices below the capacity), and the bound
on MAC tags from `NonceMACScheme.exists_sign_length_bound` (under `nonceLen n`-bit nonces), instead
of re-deriving it from `keyGen_ppt.length_le` and `sign_ppt.length_le`.

[MACScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/MAC.lean#L176) reuses `SignatureScheme.signingOracleOf` and `oneTimeSigningOracleOf` for fresh-message EUF-CMA while distinguishing it from fresh-pair SUF-CMA (`signingPairOracle`, `oneTimeSigningPairOracle`). A randomized signer can return more than one valid tag for a message, so the distinction is observable. `PseudorandomFunction.sufCma_prfMAC` proves a native PRF-based construction with forging probability bounded by reduction advantage plus `2^-n`. `NonceMACScheme` adds a nonce-respecting query condition. A stateful signer can choose the nonces itself with a counter (Boneh–Shoup §7.5): [`MAC/Counter.lean`](../../CslibFrontier/Crypto/Computational/MAC/Counter.lean) tags the `j`-th message under the `nonceLen n`-bit binary counter `BitString.lowBits (nonceLen n) j`, refuses after `2 ^ nonceLen n` tags, and states strong unforgeability as `NonceMACScheme.CounterSUFCMA`. `NonceMACScheme.SUFCMA.counterSufCma` derives it from `SUFCMA` with loss 1 through the explicit reduction `counterForger` and its certificate `isOraclePPT_counterForger`. The Carter–Wegman instance is `PseudorandomFunction.counterSufCma_carterWegmanNonceMAC` in [`MAC/CarterWegman.lean`](../../CslibFrontier/Crypto/Protocols/MAC/CarterWegman.lean).

For concrete multi-block CBC-MAC bounds and domain-separation counterexamples over `BitString n`,
import [`BlockCipher/CBCMAC.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/CBCMAC.lean)
(Katz–Lindell 3rd ed., §4.4, Construction 4.9, Theorem 4.12, Claim 4.13, and Exercises 4.13–4.16).
`cbcMacBlocks` folds `state ↦ g (state + block)` with composition law `cbcMacBlocks_append` and
last-ciphertext-block identity `getLast_cbcEncryptBlocks_eq_cbcMacBlocks`. On bounded nonempty
inputs `CBCInput n ℓ`, `cbcSmooth_of_prefixFree` proves `(q, ℓ, q^2 * ℓ^2 / 2^n)`-smoothness for
any `q` distinct prefix-free queries (`CBCPrefixFree`, `CBCSmooth`), and
`abs_cbcRealSuccess_sub_cbcIdealSuccess_le` lifts this to an adaptive PRF bound for distinguishers
written as ordinary oracle programs `OracleComp (CBCOracleSpec n ℓ) Bool`, run with the query log of
`OracleComp.interpret` (`cbcQueryRun`) and restricted on every fixed-oracle execution to a
prefix-free budget of `q` queries (`CBCAdmissible`, `cbcRealSuccess`, `cbcIdealSuccess`). The bound
is information-theoretic: no computational PRF reduction or machine-realizability is claimed. The
module also proves
probability-`1` forgery attacks for each of the six relaxations in Exercises 4.13–4.16:
variable-length extensions without prefix-freeness (`cbcTwoToFourAttack_valid`,
`cbcToThreeAttack_valid`), leaked intermediate
chaining blocks (`cbcLeakedTagsAttack_valid`), random IVs (`cbcRandomIVAttack_valid`), appended
rather than prepended message lengths (`cbcLengthSuffixAttack_valid`), and ambiguous zero padding
(`zeroPadAttack_valid`, using `List.rightpad` and the floor-count block splitter
[`BitString.padBlocks`](../../CslibFrontier/Foundations/Data/BitString/PadBlocks.lean)), with concrete
four-bit witnesses in
[`CslibFrontierTests/Crypto/CBCMAC.lean`](../../CslibFrontierTests/Crypto/CBCMAC.lean). The
query-based attacks return a `ForgeryTrace` with its `queries`, forged `message` and claimed `tag`;
`trace.Valid mac` says that the message was never queried and that `mac` gives it the claimed tag.
The random-IV attack instead transforms one observed `(iv, tag)` pair.

For variable-length messages under CBC-MAC, import
[`BlockCipher/LengthPrependedCBCMAC.lean`](../../CslibFrontier/Crypto/Primitives/BlockCipher/LengthPrependedCBCMAC.lean)
(Katz–Lindell 3rd ed., §4.4.1, Figure 4.2, and Exercise 4.18 [katzlindell20][katzlindell20]).
`lengthPrependedCbcMac` runs basic CBC-MAC on a block-aligned message of at most `L` blocks with
its encoded block count in front (`prependLength`, `blockCountBlock`). For an injective length
encoding, no prepended input is a prefix of another (`not_isPrefix_prependLength`), so
`prependLengthQueries` turns an adaptive distinguisher into a prefix-free CBC-MAC distinguisher.
`abs_lengthPrependedRealSuccess_sub_lengthPrependedIdealSuccess_le` then bounds its advantage
against a uniform random function by `q^2 * (L + 1)^2 / 2^n` for `q` queries. Like the prefix-free
bound, this statement is information-theoretic. Concrete checks are in
[`CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean`](../../CslibFrontierTests/Crypto/OFBAndLengthCBCMAC.lean).

For messages of varying length built from a fixed-length `MACScheme`, import
[`Protocols/MAC/VariableLength.lean`](../../CslibFrontier/Crypto/Protocols/MAC/VariableLength.lean)
(Katz–Lindell 3rd ed., §4.3.2, Construction 4.7 and Theorem 4.8). `MACScheme.blockwiseSign` tags
every block together with a fresh uniform identifier, the message length and the block index;
`isPPTOn_blockwiseSign`, `computableInPolyTime_blockwiseVerify` and `isPPT_blockwiseGame` certify
the honest algorithms and experiment for any `IsPolyTimeEncoder` and strict oracle-PPT
`BlockwiseMACForger`. `MACScheme.blockwiseGame_le` bounds the fresh-message EUF-CMA success
probability by the advantage of `blockwiseReduction` against the fixed-length scheme plus
`(∑ i ∈ range Q, i) / 2 ^ w` for an adversary with at most `Q` signing queries, where `w` is a
quarter of the fixed input length. Truncating fixed-length oracle replies to a polynomial bound on
honest tags yields the uniform strict oracle-PPT reduction `blockwiseBoundedReduction`
(`isOraclePPT_blockwiseBoundedReduction`), and `MACScheme.EUFCMA.blockwiseEUFCMA` derives uniform
asymptotic `BlockwiseEUFCMA fullEncoder` whenever `PolynomiallyLowerBounded M.msgLen`.
`blockwiseGame_noIndex`, `blockwiseGame_noLength` and `blockwiseGame_noIdentifier` (together with
`not_blockwiseEUFCMA_noIndexEncoder`, `not_blockwiseEUFCMA_noLengthEncoder` and
`not_blockwiseEUFCMA_noIdentifierEncoder`) show that omitting any one of the three fields gives a
strict oracle-PPT forger that wins with probability `1` once `w ≥ 3`, that is, once the fixed
input length is at least `12`. Concrete checks are in
[`CslibFrontierTests/Crypto/VariableLengthMAC.lean`](../../CslibFrontierTests/Crypto/VariableLengthMAC.lean).

A weak pseudorandom function only has to look random on uniformly random inputs. In
[`Computational/WeakPRF.lean`](../../CslibFrontier/Crypto/Computational/WeakPRF.lean)
(Katz–Lindell 3rd ed., Exercises 3.28 and 4.9 [katzlindell20][katzlindell20]),
`WeakPseudorandomFunction` gives the distinguisher an oracle that returns a fresh uniform input
together with its value under the keyed function or under a random function, and
`PseudorandomFunction.weakPseudorandomFunction` proves that every pseudorandom function is weak.
The converse fails: `zeroPatch` maps the all-zero input to itself and leaves every other value
unchanged. `advantage_weakPrfRealGame_zeroPatch_le` shows that the patch moves the weak real game
by at most `Q / 2 ^ n` against an adversary making at most `Q` calls, so
`WeakPseudorandomFunction.zeroPatch` keeps weak security, while
`not_pseudorandomFunction_zeroPatch` and `not_eufCma_prfMAC_zeroPatch` show that the patched
family is not pseudorandom and that its direct MAC is forgeable with probability `1`. From any pseudorandom function this
gives `PseudorandomFunction.exists_weak_not_pseudorandom` and
`PseudorandomFunction.exists_weak_not_eufCma_prfMAC`. Another answer to Exercise 3.28(b)
evaluates the function after rounding odd inputs to even ones; the zero patch is simpler and
separates the same notions. Encryption from a weak pseudorandom function (Exercise 3.28(d)) is not formalized.

For fixed-length coefficient-vector hashing, import
[`Probability/HashFamily/Polynomial.lean`](../../CslibFrontier/Probability/HashFamily/Polynomial.lean).
`coeffPolyHash k x` performs the `n` Horner multiply-add rounds for `x : Fin n → F`, and
`coeffPolyHashLinear` packages its linearity in `x`. The public
`coeffPolyHash_eq_polynomialHash_rev` bridge identifies it with the existing ascending-coefficient
`polynomialHash` after `Fin.rev`; `polyHash_ofFn_eq` identifies the existing monic variable-length
evaluator with `k ^ n + coeffPolyHash k x`. The separate Horner surface retains source coefficient
order and a one-pass executable fold. If the evaluation point is uniform in a finite seed type `S`
injected into the field, `isUniversalHash_coeffPolyHash_of_embedding` gives the conservative
collision bound `n / |S|`; `isUniversalHash_coeffPolyHash` specializes it to the full field. This
is the restricted-domain polynomial-evaluation fact used in
[FAEST v3 §4.2](https://faest.info/faest-spec-v3.0.pdf), including its 64-bit ZKHash challenge,
but it does not construct that embedding or compose VOLEHash/ZKHash. The evaluator records exact
field-operation counts. Its generic auxiliary state is `b + O(log n)` bits for a `b`-bit field
accumulator and runtime index, before field-operation scratch; generic static control is independent
of `n`. An unrolled specialization uses `O(n)` field-operation nodes and can omit the runtime index.
No polynomial-time claim is made without encoded field operations and a certified sampler.

For polynomial-evaluation hashing of messages shorter than `ℓ` over a finite field, import
[`Protocols/MAC/PolynomialEvaluation.lean`](../../CslibFrontier/Crypto/Protocols/MAC/PolynomialEvaluation.lean)
(Katz–Lindell 3rd ed., §4.5.2, Theorem 4.17 and Exercise 4.22). A message with its length code
appended is evaluated at the key in one of four coefficient layouts.
`PolynomialEvaluation.isDeltaUniversalHash_hash` proves the textbook layout `ℓ / |F|`-difference
universal for any injective length code. For the layouts of Exercise 4.22(a) and (c),
`isDeltaUniversalHash_fixedTopHash` and `isDeltaUniversalHash_ascendingHash` prove the same bound
when, in addition, no positive length is coded as zero, and `not_isDeltaUniversalHash_fixedTopHash`
and `not_isDeltaUniversalHash_ascendingHash` give a key-independent collision when the length `1`
is coded as zero. For `1 < ℓ` and `ε < 1`, the constant-term layout of Exercise 4.22(b) is never
`ε`-difference universal (`not_isDeltaUniversalHash_constantTermHash`). Concrete checks over
`ZMod 5` and for the zero patch are in
[`CslibFrontierTests/Crypto/WeakPRFAndPolyMAC.lean`](../../CslibFrontierTests/Crypto/WeakPRFAndPolyMAC.lean).

[IndexedSignatureScheme](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/Complexity/Crypto/Computational/IndexedSignature.lean#L89) signs index/message pairs with polynomially bounded capacity; the oracle refuses repeated or out-of-range signing indices. The syntax is stateless but the game enforces single use. Counter wrappers and Merkle signature clients turn that contract into stateful signing, whereas [TreeSignature.scheme](../../CslibFrontier/Crypto/Computational/TreeSignature.lean#L576) and [TreeSignature/Security.lean](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4289) upgrade any indexed EUF-CMA scheme of capacity at least `2` plus a pseudorandom function (or one-way function) to a stateless `SignatureScheme` (`eufCMA_scheme`, `IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`, `exists_eufCMA_of_oneWay`) by sampling a uniform leaf and deriving internal node keys and signing coins from the PRF [bs23][bs23]; `TreeSignature.sign` returns `[]` outside the `n`-bit message domain. Composing Lamport, depth-`1` Merkle trees, PRFs from one-way functions, and stateless tree signatures gives [OneWay.exists_eufCMA_of_hashFamily](../../CslibFrontier/Crypto/Computational/TreeSignature/Security.lean#L4347) from a one-way function and a collision-resistant hash family. Without full collision resistance, [`TCRSignature.scheme`](../../CslibFrontier/Crypto/Computational/TCRSignature.lean) adapts Boneh–Shoup §13.2.1, construction `(13.2)` on p. 533 and Theorem 13.2 on p. 534 [bs23][bs23] to a capacity-`1` `IndexedSignatureScheme` over a one-time signature scheme `S` and an unrestricted target collision-resistant `KeyedHashFamily` `H` without storing a hash key in `pk` (`SignatureScheme.OneTimeEUFCMA.indexedEUFCMA_tcrSignature`; concrete checks and an explicit `1`-probability break against a constant hash family are in [`CslibFrontierTests/Crypto/TCRSignature.lean`](../../CslibFrontierTests/Crypto/TCRSignature.lean)), and [`IndexedSignatureScheme.double`](../../CslibFrontier/Crypto/Computational/IndexedSignature/Double.lean) doubles any indexed scheme of capacity at least `1` to constant capacity `2` with plug-and-pray loss `2` (Boneh–Shoup §14.6.1, construction `(14.4)` on p. 597, and Exercise 13.2 [bs23][bs23]; `IndexedSignatureScheme.IndexedEUFCMA.double`). Composing Lamport one-time signatures, `TCRSignature.scheme`, `IndexedSignatureScheme.double`, and `TreeSignature` yields `OneWay.exists_eufCMA_of_targetCollisionResistant`: instantiating `H` with `naorYungHash` proves `OneWayPermutation.exists_eufCMA` (Naor–Yung §4 / Theorem 2 [naoryung89][naoryung89]), while instantiating `H` with `rompelHash` in [`Rompel.lean`](../../CslibFrontier/Crypto/Computational/Rompel.lean) removes the permutation hypothesis to yield `OneWay.exists_indexedEUFCMA_two` and `OneWay.exists_counterEUFCMA_two` on arbitrary-length `List Bool` messages, `OneWay.exists_eufCMA` and `exists_oneWay_iff_exists_signature` on `SignatureScheme`'s `n`-bit message domain, and—after applying [`TCRSignature.wordScheme`](../../CslibFrontier/Crypto/Computational/TCRSignature/ManyTime.lean) (`SignatureScheme.EUFCMA.eufCMA_wordScheme`)—`OneWay.exists_wordEUFCMA` and `exists_oneWay_iff_exists_wordSignature` on unrestricted `List Bool` messages ([rompel90][rompel90]; client checks and message-space separation witnesses in [`CslibFrontierTests/Crypto/Rompel.lean`](../../CslibFrontierTests/Crypto/Rompel.lean)). Keep the indexed game's no-repeat invariant distinct from durable storage in a deployed stateful implementation: no filesystem or crash-recovery model is asserted here.

Collision-resistant hashing alone gives these stateless signatures.
[`HashFamily.oneWay_keyDigest`](../../CslibFrontier/Crypto/Computational/CollisionResistantToOneWay.lean)
proves that `keyDigest H`, which reads its input as a key `k` (the first third) and a message `x`
and outputs `k ++ H k x`, is one-way for every collision-resistant hash family `H` (Katz–Lindell,
Exercise 8.4). An inverter either finds a collision under the uniform key or returns `x` itself;
since it sees the `(2 n + r)`-bit message only through its `n`-bit digest, the latter happens with
probability at most `(1 / 2) ^ n`. Composed with `OneWay.exists_eufCMA` and
`OneWay.exists_wordEUFCMA`, this gives `HashFamily.exists_eufCMA` and `HashFamily.exists_wordEUFCMA`
(Katz–Lindell, Theorem 14.16), so the one-way function assumed by
`OneWay.exists_eufCMA_of_hashFamily` follows from its hash family. Through Merkle–Damgård (the
one-bit-per-block instance `merkleDamgard`, not the length-strengthened one),
`CompressionFamily.exists_oneWay` and `CompressionFamily.exists_wordEUFCMA` give the same
conclusions for `2 n → n` compression families. No converse is claimed.

Merkle–Damgård chains have many messages with one digest at little more than the cost of one
collision (Joux's attack, [bs23][bs23], §8.4.1, pp. 298–299). Import
[`MerkleDamgard/Multicollision.lean`](../../CslibFrontier/Crypto/Computational/MerkleDamgard/Multicollision.lean).
Its finders reach the compression function only as an oracle. Their certificates
(`ProbOracleComp.IsQueryBounded`) bound the number of compression calls on every path, the cost
measure of §8.3; they are not running times, since sampling and the search for a colliding pair
are not counted, and they are worst-case counts, not expected costs. Let `h k` map `n + ℓ`-bit
inputs to `n`-bit outputs (`hlen`), let `iv` have `n` bits (`hiv`), let `n + 7 ≤ ℓ`, and let
`s = ⌈2 √(2 ^ n)⌉₊ + 1`. Then `merkleDamgardJouxFinder ℓ s (3 * b) b iv` makes at most
`3 * b * s` calls (`isQueryBounded_merkleDamgardJouxFinder`), and with probability at least `1/2`
it returns `b` pairs of blocks such that, for every common list of blocks `tail`, their `2 ^ b`
selections, each followed by `tail`, have one `merkleDamgardChain` value from `iv`
(`merkleDamgardJouxFinder_success_half`; `mem_multicollisionOutputs` unfolds the event);
`merkleDamgardJouxFinder_success` gives the bound for any `s` and budget. For the library's
one-bit-per-block `merkleDamgard`, let `h k` map `2 * k.length`-bit inputs to `k.length`-bit
outputs, let groups have `g` bits with `k.length + 7 ≤ g`, and let `s = ⌈2 √(2 ^ k.length)⌉₊ + 1`.
Then `merkleDamgardBitJouxFinder k.length g s (3 * b) b` makes at most `1 + 3 * b * (s * g)` calls
and with probability at least `1/2` returns `b` pairs of groups whose `2 ^ b` selections are a
`2 ^ b`-collision of `merkleDamgard h k` (`merkleDamgardBitJouxFinder_success_half`;
`mem_bitMulticollisionOutputs` unfolds the event). One call per message bit puts a factor `g` in this
count that the book's count does not have. Each attempt runs the birthday finder of
[`CollisionResistant/Birthday.lean`](../../CslibFrontier/Crypto/Computational/CollisionResistant/Birthday.lean).
Let `M` be a finite nonempty type, let `M` and `T` have decidable equality, let `O` be a
deterministic oracle, let every value of `f : M → T` lie in a finite set `D` (`hf`), let `digest m`
return `f m` when run against `O` (`hdigest`), and let `100 * D.card ≤ Fintype.card M`. Then
`⌈2 √|D|⌉₊ + 1` uniform messages give two different messages with one value of `f` with
probability at least `1/2` (`birthdayFinder_success_book`; [bs23][bs23], §8.3, Lemma 8.2,
p. 294). The collision for `H₁ ‖ H₂` at the end of §8.4.1 is not stated. The checks in
[`CslibFrontierTests/Crypto/MerkleDamgardMulticollision.lean`](../../CslibFrontierTests/Crypto/MerkleDamgardMulticollision.lean)
show that 45 calls give an 8-collision with probability at least `3/4` for every compression
function with one-bit chaining values and eight-bit blocks.

## Commitments and ideal distributions

To state a commitment scheme and its games as programs, import [Commitment/Scheme.lean](../../CslibFrontier/Crypto/Computational/Commitment/Scheme.lean). `Commitment.Scheme K M C O` has typed key, message, commitment and opening spaces, with key generation and commitment as `ProbComp` programs and a Boolean `verify`. `hidingExperiment` draws a key and runs `lrExperiment` on the commitment component. `bindingExperiment` asks for a `BindingCollision`, two distinct messages opened against one commitment. `PerfectlyHidingAt S k` makes every message's commitment law equal at key `k`. At such a key, the left-or-right advantage is zero (`Scheme.advantage_lrExperiment_eq_zero`). `Scheme.advantage_hidingExperiment_le` bounds the hiding advantage by the probability that key generation lands outside a perfectly hiding set. The Pedersen instance `pedersen d` at a fixed group description is correct (`pedersen_correct`) and perfectly hiding at every key `h ≠ 0` (`pedersen_perfectlyHidingAt`). The zero key, drawn with probability `1 / q`, is the only loss, so `advantage_pedersen_hidingExperiment_le` gives at most `1 / q`. `succProbability_pedersen_bindingExperiment_le` bounds binding by the discrete-logarithm advantage of the explicit reduction `pedersenToDL`, which reads off `α = (r₁ - r₀)⁻¹ * (m₀ - m₁)` from two openings. These are fixed-parameter statements and make no efficiency claim. The [checked clients](../../CslibFrontierTests/Crypto/CommitmentScheme.lean) cover a perfectly hiding scheme whose binding success is one; the [Pedersen clients](../../CslibFrontierTests/Crypto/PedersenCommitment.lean) instantiate both bounds on a group of order `11`.

[CommitmentScheme](../../CslibFrontier/Crypto/Computational/Commitment/Basic.lean) is the older word-level interface and is intentionally distributional: it gives a faithful public-key encoding, valid messages, an exact `PMF` of commitment/opening pairs (`commitDist`), verification and correctness, and its keys come from an external setup law. For Pedersen, `pedersenHidingGame_eq` and `pedersenBindingGame_eq` state that its word-level games equal the typed experiments of `pedersen d` under `pedersenKeyDist`.

[`Commitment/PublicOperations.lean`](../../CslibFrontier/Crypto/Computational/Commitment/PublicOperations.lean), [`PedersenCommitment/PublicOperations.lean`](../../CslibFrontier/Crypto/Computational/PedersenCommitment/PublicOperations.lean) (`validPedersenMessageBool`, `encodePedersenVerify`), and [`PedersenCommitment/ProbComp.lean`](../../CslibFrontier/Crypto/Computational/PedersenCommitment/ProbComp.lean) supply the strict-PPT public operations and bounded fair-coin samplers. Specifically, `pedersenCommitProb` and `pedersenKeyGenProb` sample their exponents via `sampleExp` (certified `IsPPTOn` by `isPPTOn_pedersenCommitProb` and `isPPTOn_pedersenKeyGenProb`), and `pedersenKeyDistProb` draws `d ← setup n` followed by `pedersenKeyGenProb n d`. Replacing ideal commitment sampling (`commitDist`) with `pedersenCommitProb` or ideal key generation (`pedersenKeyDist`) with `pedersenKeyDistProb` shifts any Boolean continuation by at most `1 / 2 ^ n` (`advantage_bind_pedersenCommitProb_le`, `advantage_bind_pedersenKeyGenProb_le`, `advantage_bind_pedersenKeyDistProb_le`).

Because `CommitmentScheme.commitDist` does not take the accuracy parameter `n : ℕ`, `pedersenScheme.hidingGame (F.pedersenKeyDistProb setup)` replaces only key generation with `sampleExp` (giving advantage at most `1 / m + 2 / 2 ^ n` via `advantage_pedersenHidingGame_pedersenKeyDistProb_le` and `pedersenScheme_statisticalHiding_pedersenKeyDistProb`), while `CommitmentScheme.bindingGame` never invokes `commitDist` (`DiscreteLog.pedersenScheme_binding_pedersenKeyDistProb`). For chosen-message hiding where the challenger also samples the challenge commitment with `pedersenCommitProb`, use `pedersenHidingProbForKey` at a fixed key `h ≠ 0` (advantage at most `2 / 2 ^ n`, `advantage_pedersenHidingProbForKey_le_of_ne_zero`) and `pedersenHidingProbGame` under `pedersenKeyDistProb` (advantage at most `1 / m + 4 / 2 ^ n`, `advantage_pedersenHidingProbGame_le`, `negligible_advantage_pedersenHidingProbGame`). At a fixed group description `d`, `pedersenHidingProbExperiment` is the executable `ProbComp Bool` realization of `pedersenHidingProbGame` (`bind_eval_pedersenHidingProbExperiment`, `isPPTOn_pedersenHidingProbExperiment`); see [`Crypto/PedersenSampling.lean`](../../CslibFrontierTests/Crypto/PedersenSampling.lean).

## Garbling schemes

[Garbling/Scheme.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Scheme.lean) is the abstract garbling-scheme syntax of Bellare, Hoang and Rogaway, Sections 3 and 4 [bhr12][bhr12]: `Scheme Fn` is `(Gb, En, De, Ev, ev)` over an abstract type of function descriptions with length readers, `Scheme.Garbled` is the output triple `(F, e, d)`, and `Query Fn` is a query `(f, x)`. `Gb` carries its coins explicitly (`coinLen` and a deterministic `gb`), and `Scheme.garble` samples them via `BitString.sampleList`, so non-degeneracy can quantify over the coins (`Scheme.eval_garble`, `Scheme.mem_support_eval_garble_iff`). `Scheme.IsValid` bundles `Scheme.LengthCondition`, `Scheme.NonDegenerate` and `Scheme.Correct`; `Scheme.WellTyped` fixes the output length of `ev` and of every successful decoding of an arbitrary string. A `SideInfo Fn Λ` is a side-information function `Φ` with length readers (`SideInfo.circ` is the identity side information `Φ_circ`), and `SideInfo.Compatible`, `SideInfo.IsEvInverter` and `SideInfo.IsInverter` are the compatibility condition of Section 3.3 and the inversion hypotheses of Section 4.1 (`SideInfo.Compatible.inLen_eq`, `SideInfo.circ_compatible`, `SideInfo.circ_isInverter`). For a concrete point-and-permute circuit garbling construction over `Cslib.Circuits.Circuit`, see [Protocols and privacy](protocols-and-privacy.md#garbled-circuits); `PointPermute.scheme` there is that construction as a valid `Scheme ValidCircuit`.

[Garbling/Games.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Games.lean) states the single-query games of Sections 3.4–3.6 as experiments at a fixed security parameter `k`: `prvIndExperiment`, `prvSimExperiment`, `obvIndExperiment`, `obvSimExperiment` and `autExperiment`. Their adversaries are `TwoStage` adversaries (`PrvIndAdversary`, `PrvSimAdversary`, `ObvIndAdversary`, `ObvSimAdversary`, `AutAdversary`) that choose a `Query` or a `MessagePair` of queries and keep a state; the views are the records `PrvView` `(F, X, d)` and `ObvView` `(F, X)`, the real views are `Scheme.prvView` and `Scheme.obvView`, and the simulators `PrvSimulator` and `ObvSimulator` work at the fixed parameter. The advantages (`prvIndAdvantage`, `prvSimAdvantage`, `obvIndAdvantage`, `obvSimAdvantage`, `autAdvantage`) are `Experiment.advantage` and `Experiment.succProbability`. An invalid pair (`prvIndValid`, `obvIndValid`) or query is answered by `⊥`, so these are not `lrExperiment` instances; `prvIndAdvantage_eq_zero_of_invalid` records that an always-invalid adversary has advantage `0`, and `prvIndAdvantage_eq_two_mul_guessingAdvantage` identifies the `prv.ind` advantage with twice the bias of `Experiment.guessBit (prvIndExperiment G Φ k A)`. [Garbling/Foundations.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Foundations.lean) proves Propositions 2 and 3 (Section 4) as exact per-adversary identities: `prvIndAdvantage_eq_two_mul_prvSimAdvantage_prvIndToSim` for every simulator (`prvIndToSim`, state `IndToSimState`) and `prvSimAdvantage_prvSimFromInverter_eq` against the inverter simulator `prvSimFromInverter` (`prvSimToInd`, `eval_prvSimExperiment_prvSimFromInverter`) under an `ev`-inverter, together with the obliviousness analogues (`obvIndToSim`, `obvSimFromInverter`, `obvInverterQuery`, `obvSimToInd`, `obvIndAdvantage_eq_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_eq`, `eval_obvSimExperiment_obvSimFromInverter`) under an inverter and `≤` corollaries (`prvIndAdvantage_le_two_mul_prvSimAdvantage_prvIndToSim`, `prvSimAdvantage_prvSimFromInverter_le`, `obvIndAdvantage_le_two_mul_obvSimAdvantage_obvIndToSim`, `obvSimAdvantage_obvSimFromInverter_le`). [Garbling/CircuitInverters.lean](../../CslibFrontier/Crypto/Primitives/Garbling/CircuitInverters.lean) specialises this framework to conventional Boolean circuits (`ConventionalCircuit`, `ValidCircuit`, `Topo`, the well-formedness structure `Topo.IsValid`, `ValidTopo` and the shape record `ValidShape` of Section 2.3; `Scheme.IsCircuitScheme`) and the three standard side-information functions `phiTopo`, `phiSize` and `phiCirc` (`phiTopo_compatible`, `phiSize_compatible`, `phiCirc_compatible`). It constructs the explicit deterministic `(Φ, ev)`-inverters `mTopo` and `mSize` (`mTopoGates`, `sizeTopo`) and `Φ`-inverters `mTopoInv` and `mSizeInv` of Section 4.1, Proposition 1 (`phiTopo_isEvInverter`, `phiSize_isEvInverter`, `phiTopo_isInverter`, `phiSize_isInverter`, `phiCirc_isInverter`), and derives Corollaries 1 and 2 of Sections 4.2–4.3 (`prvIndAdvantage_phiTopo_eq_two_mul_prvSimAdvantage`, `prvSimAdvantage_phiTopo_mTopo_eq`, `prvIndAdvantage_phiSize_eq_two_mul_prvSimAdvantage`, `prvSimAdvantage_phiSize_mSize_eq`, and the obliviousness analogues for `phiTopo`, `phiSize` and `phiCirc`). [Garbling/Adaptive.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Adaptive.lean) adds the coarse-grained adaptive privacy game `Prv1` of Bellare, Hoang and Rogaway, Section 3.1, Figure 2 [bhr12b][bhr12b] (`GarbledFn`, `Prv1Adversary`, `Prv1Simulator`, `prv1Experiment`, `prv1Advantage`, `prv1Advantage_eq_two_mul_guessingAdvantage`); its adversary has three stages, so it is not a `TwoStage` adversary. The embedding `prvSimToPrv1` and induced simulator `prv1SimulatorToPrv` (`PrvSimToPrv1State`) show that adaptive `prv1` simulation security implies selective `prv.sim` security with exact advantage equality (`eval_prv1Experiment_prvSimToPrv1`, `prvSimAdvantage_prv1SimulatorToPrv_eq`) and selective `prv.ind` security with a factor of two (`prvIndAdvantage_eq_two_mul_prv1Advantage`). [Garbling/Efficient.lean](../../CslibFrontier/Crypto/Primitives/Garbling/Efficient.lean) defines `Scheme.IsEfficient G encFn` (polynomial-time length readers, coin count, `gb`, `En`, `Ev`, `De` and `ev` on encoded arguments; Section 3.1 asks for linear-time length readers) and the circuit encodings `encConventionalCircuit` and `encValidCircuit` (`n`, `m` in unary, wire numbers in binary, truth tables as four bits); `PointPermute.scheme_isEfficient` in [Garbling/PointPermute/Efficient.lean](../../CslibFrontier/Crypto/Primitives/Garbling/PointPermute/Efficient.lean) proves it for point-and-permute garbling over any polynomial-time family. No negligible-advantage statement is made, and projective schemes (`Π` of Section 3.2) and the authenticity relations of Section 4 are not part of these modules. [Garbling-scheme clients](../../CslibFrontierTests/Crypto/GarblingScheme.lean) and [inverter/adaptive clients](../../CslibFrontierTests/Crypto/GarblingInverters.lean) check valid schemes (`identityScheme`, `plainCircuitScheme`), verify zero advantage for an invalid-query adversary, separate `phiSize`, `phiTopo` and `phiCirc` on concrete valid circuits, execute `mTopo` and `mSize` by `decide`, and instantiate the `prv.sim`, `obv.sim` and `prv1` reductions.

## Known Limitations

The finite query-only PRG/cipher results, semantic commitment interfaces and uniform native primitive structures do not share one implicit efficiency premise. The table records the differences. The long internal HILL and GGM proofs, all serialization helpers, and every named reduction were not independently re-proved or built in this pass. Existing nonvacuity tests are useful checks of interfaces, not evidence that cryptographic hardness assumptions hold.

[acek17]: ../sources.md#acek17
[bhr12]: ../sources.md#bhr12
[bhr12b]: ../sources.md#bhr12b
[bs23]: ../sources.md#bs23
[complexitylib]: ../sources.md#complexitylib
[cs03]: ../sources.md#cs03
[cslib]: ../sources.md#cslib
[falcon2020]: ../sources.md#falcon2020
[fips1804]: ../sources.md#fips1804
[fips202]: ../sources.md#fips202
[fips203]: ../sources.md#fips203
[fips205]: ../sources.md#fips205
[fly22]: ../sources.md#fly22
[fmr20]: ../sources.md#fmr20
[ggm86]: ../sources.md#ggm86
[goldreich04]: ../sources.md#goldreich04
[hhk17]: ../sources.md#hhk17
[hhrvw20]: ../sources.md#hhrvw20
[hill99]: ../sources.md#hill99
[holenstein06]: ../sources.md#holenstein06
[katzlindell20]: ../sources.md#katzlindell20
[kyber302]: ../sources.md#kyber302
[manin56]: ../sources.md#manin56
[naoryung89]: ../sources.md#naoryung89
[rompel90]: ../sources.md#rompel90
[uov26]: ../sources.md#uov26
