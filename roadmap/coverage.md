# Roadmap: Coverage and reuse

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

The long-term bar is to support formalizing every paper in the [Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/), with the additional work per paper increasingly its new mathematics: standard models, representation changes, reductions, resource certificates and proof techniques come from the library.
Use a growing, source-pinned sample of papers, including some chosen after an API was designed, as demanding clients, and promote recurring obligations into shared APIs only after reuse is demonstrated.

- **Arora–Barak coverage** ([#4711](https://github.com/cslib-community/cslib-frontier/issues/4711)): audit the draft against library statements and track remaining endpoints, including formal-measure density amplification with the additive loss in Razborov–Rudich Theorem 5.1(b) (omitted in draft Theorem 22.3), general integer programming in `NP` (draft Theorem 2.17), which needs Papadimitriou's polynomial-bit small-solution bound, and the bridge from visited-cell space to the draft's ever-non-blank space measure that the completeness results for `PATH` (draft Theorem 4.16) and strongly connected digraphs (Exercise 4 §4) need for the draft's classes.
- **Measure postprocessing** ([#2732](https://github.com/cslib-community/cslib-frontier/issues/2732)): Canonical full-L1 total variation contracts under measurable maps of arbitrary finite measures, including unequal masses.
  Its consumer is the Gaussian projection and mod-one bound ([#2734](https://github.com/cslib-community/cslib-frontier/issues/2734)).
- **Finite weighted measure mixtures:** Bound the full-L1 distance when both the finite component measures and their nonnegative weights change, keeping the comparison components' total masses explicit so that neither probability normalization nor equal masses is required.
  The tagged finite-PMF form supplies the error-composition step for the Regev LWE experiment ([#2767](https://github.com/cslib-community/cslib-frontier/issues/2767)); identifying and bounding its conditional laws belongs to that issue.
- **Gaussian density and projection laws** ([#2733](https://github.com/cslib-community/cslib-frontier/issues/2733)): Identify the positive-width normalized Gaussian weight with a scaled standard Gaussian, whose scalar projections have variance `(s ‖z‖)² / (2π)`, including the zero vector and dimension zero.
  Prove the discrete-coset convolution projection and mod-one bound ([#2734](https://github.com/cslib-community/cslib-frontier/issues/2734)); efficient sampling and the quantum reduction belong to [#1213](https://github.com/cslib-community/cslib-frontier/issues/1213).
- **One sensitivity API:** Define the sensitivity measures over any `Fintype` in CSLib and drop the separate measures of the sensitivity-separation development.
- **Indicator-expectation and conversion lemmas:** Factor the indicator-expectation identities from PCP's second-moment calculation, and recurring cardinality and logarithm conversions, once a second client benefits.
- **Divide-and-conquer recurrences** ([#3042](https://github.com/cslib-community/cslib-frontier/issues/3042)): A master theorem over `ℕ` with explicit constants for inequality recurrences in all three polynomial cases, with `IsBigO` forms, matching `Θ` bounds for equality recurrences, and case 3 under the general regularity condition.
  Move hand-solved recurrences onto it where the generic constant suffices, keeping CSLib's sharper merge-sort bound and the halving lemma, the sharp tool for `b = 2`.

### OpenAI math results ([#1002](https://github.com/cslib-community/cslib-frontier/issues/1002))

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the openai/math release, and extract the in-scope results, both headline theorems and minor lemmas useful in their own right.
Prove each against cslib-frontier's definitions from the cited manuscript's exact statement with its version pinned, labelling unrefereed results; a source formalization is a reference, not evidence.
The openai/math formalizations are Apache 2.0, as is cslib-frontier, so adaptation with attribution is permitted; the rewrites state no license and are only read and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/cslib-frontier/issues/1538)): A `#k`-SAT model counter running in time `2^{O_k(n log log n / √log n)}` at arbitrary density, by recursive tensor contraction.
  The intended route combines the fixed-density bound `2^{O_{k,D}(n / √log n)}` (Theorem D.1 with `ℓ = 1`) with the Lemma D.2 construction, applied natively to the model-counter interface.
- **Exact optimization:** Exact MAX-SAT score distributions and optima in contraction time measured by literal occurrences plus clauses, with `2^{O_{k,c}(n / √log n)}` time and polynomial space for sparse fixed-width instances, and native extraction of an optimizing assignment.
  Neither these bounds nor ordinary SAT sparsification gives a variable-count rate for dense exact MAX-SAT.
- **Large weights:** Exact contraction of natural tensor tables whose bit lengths are polynomial in the structural size, applied natively to weighted-CSP partition functions, and signed or rational weight interfaces.
