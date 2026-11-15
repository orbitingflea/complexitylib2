# Roadmap

The directions cslib-frontier aims to cover.
This file holds the programs and the index; the directions are listed by area in the files under [roadmap/](roadmap/), one file per area, so that changes in different areas do not conflict.
The roadmap lists directions only: status, progress and completion notes live on the linked issues and pull requests, module docstrings describe what is proved, and the [results inventory](results/README.md) collects completed named results.
A PR edits a roadmap file only when it opens or closes a direction.
Each entry states its direction's scope in at most a few sentences, one sentence per line.
A direction leaves the roadmap only when it is completed or deliberately dropped, and there is no deferred tier.

A direction is complete only when its machine, resource and quantitative conclusions are proved for the actual algorithms, with explicit models, encodings and assumptions.
An abstract algorithm, a class definition or an assumed reconstruction theorem does not complete it.
Search Mathlib, CSLib and this library before starting, and check upstream work.

The [pre-rewrite roadmap](https://github.com/cslib-community/cslib-frontier/blob/c89dd48c/ROADMAP.md) is the archive of past detail and design records, including the FHE industrial context, the first-order design decisions and the repository's history.
The [version before the scope-only rewrite of 2026-11-08](https://github.com/cslib-community/cslib-frontier/blob/9886447e2/ROADMAP.md) holds the progress notes removed in that rewrite.

## Programs

| Program | Issues |
| --- | --- |
| Frontier program: ambitious theorems toward the research frontier | [#897](https://github.com/cslib-community/cslib-frontier/issues/897); its tracks are linked below |
| Optional experiment: formalize unformalized STOC 2027 submission results, subject to independent source-correspondence review | [#2527](https://github.com/cslib-community/cslib-frontier/issues/2527) |
| Metacomplexity: time-bounded Kolmogorov complexity, partial MCSP, hardness magnification | [#798](https://github.com/cslib-community/cslib-frontier/issues/798), cleanup [#4644](https://github.com/cslib-community/cslib-frontier/issues/4644) |
| Plain computability: delete the tidy calculus, keeping a machine-level kernel | [#862](https://github.com/cslib-community/cslib-frontier/issues/862), from [#456](https://github.com/cslib-community/cslib-frontier/issues/456) |
| Consolidation: duplicates, accurate statements and docs, less churn | [#949](https://github.com/cslib-community/cslib-frontier/issues/949) |
| Fully homomorphic encryption: follow-ups to the instantiated bootstrapping theorem, then modern schemes | [#2585](https://github.com/cslib-community/cslib-frontier/issues/2585) |
| Boneh–Shoup cryptography tracks; zero-knowledge architecture | [#640](https://github.com/cslib-community/cslib-frontier/issues/640), [#643](https://github.com/cslib-community/cslib-frontier/issues/643) |
| Crypto frontier track: Kilian's succinct arguments | [#999](https://github.com/cslib-community/cslib-frontier/issues/999) |
| OpenAI math TCS results: review Fortnow's rewrites and extract in-scope results | [#1002](https://github.com/cslib-community/cslib-frontier/issues/1002) |
| A Verso guide with a chapter per area | [#585](https://github.com/cslib-community/cslib-frontier/issues/585) |
| Randomized Word RAM: broader expected-time rules and simulation bridges | [#1124](https://github.com/cslib-community/cslib-frontier/issues/1124) |
| Proof automation: predictable polynomial-time certificate search | [#1155](https://github.com/cslib-community/cslib-frontier/issues/1155) |
| Statistical learning theory: the textbook pillars still missing from the PAC, Rademacher and online layers, and links to cryptography and complexity | [#4920](https://github.com/cslib-community/cslib-frontier/issues/4920); directions under [learning](roadmap/models.md) |

### Landmark theorems, in priority order

Priorities live in this list and in the tiers of [#897](https://github.com/cslib-community/cslib-frontier/issues/897).

1. [Completeness of oblivious transfer](roadmap/cryptography.md#cryptographic-landmarks)
2. [Håstad's optimal MAX-E3SAT hardness](roadmap/complexity.md#approximation-and-pcp) ([#886](https://github.com/cslib-community/cslib-frontier/issues/886))
3. [Williams's NEXP ⊄ ACC⁰](roadmap/circuits.md) ([#889](https://github.com/cslib-community/cslib-frontier/issues/889))
4. [Valiant's VNP-completeness of the permanent](roadmap/circuits.md) ([#321](https://github.com/cslib-community/cslib-frontier/issues/321))
5. [The Kabanets–Impagliazzo theorem](roadmap/circuits.md) ([#891](https://github.com/cslib-community/cslib-frontier/issues/891))
6. [MIP = NEXP](roadmap/complexity.md#interactive-proofs) ([#892](https://github.com/cslib-community/cslib-frontier/issues/892))
7. [Regev's worst-case to average-case reduction](roadmap/cryptography.md#cryptographic-landmarks)

### Optional landmark projects

These are optional coverage targets outside the priority queue above, each requiring substantial new proof infrastructure; a prerequisite milestone does not complete the landmark.
Choose a source version and proof route before implementation, and reassess scope against existing library and upstream developments.
The size labels describe prerequisite breadth, not staffing or calendar estimates.

- **Babai: graph isomorphism in quasipolynomial time — optional, very large**: Prove a deterministic `exp((log n)^O(1))` decision bound for the existing encoded graph-isomorphism problem, following the [manuscript](https://arxiv.org/abs/1512.03547v2) with its [January 2017 correction](https://people.cs.uchicago.edu/~laci/upcc-fix.pdf).
  It needs certified permutation-group algorithms, the Luks framework, local certificates and the full recursion with native quasipolynomial runtime.
  An NP verifier is not the required decision algorithm.
- **Bulatov–Zhuk: the finite-domain CSP dichotomy — optional, very large**: For every fixed finite constraint language, prove its CSP is in P or NP-complete, following the tractability route of either [Bulatov](https://arxiv.org/abs/1703.03021) or [Zhuk](https://arxiv.org/abs/1704.01914v11), not both.
  The tractability algorithm has a native polynomial bound, with template-dependent constants kept separate from instance size.
  Special cases and reductions are milestones, not the full dichotomy.
- **QIP = PSPACE — optional, large**: Following [Jain–Ji–Upadhyay–Watrous](https://cs.uwaterloo.ca/~watrous/Papers/QIPequalsPSPACE.pdf), prove both inclusions for polynomial-time quantum interactive proofs with a uniform verifier, unrestricted prover strategies and explicit completeness and soundness gaps.
  The upper bound needs a polynomial-space matrix multiplicative-weights argument with controlled precision; quantum circuit simulation alone does not provide it.
- **MIP\* = RE — optional, large integration project; exceptional if rebuilt from scratch**: Prove the characterization of RE in [Ji–Natarajan–Vidick–Wright–Yuen, v4](https://arxiv.org/abs/2001.04383v4) as a native class equality, with finite-dimensional tensor-product strategies, their supremum over unbounded finite dimensions and a uniform polynomial-time verifier.
  Distinguish classical MIP from commuting-operator models.
  Start by auditing reuse of the Apache-2.0 [MIPRE formalization](https://github.com/vidick/MIPRE-formalization) rather than duplicating its compression proof.

## Areas

| Area | File |
| --- | --- |
| Cryptography | [roadmap/cryptography.md](roadmap/cryptography.md) |
| Complexity classes and reductions | [roadmap/complexity.md](roadmap/complexity.md) |
| Circuits and algebraic complexity | [roadmap/circuits.md](roadmap/circuits.md) |
| Pseudorandomness, coding and Boolean analysis | [roadmap/pseudorandomness.md](roadmap/pseudorandomness.md) |
| Communication, queries, learning and other models | [roadmap/models.md](roadmap/models.md) |
| Algorithms and optimization | [roadmap/algorithms.md](roadmap/algorithms.md) |
| Machines, RAM and data structures | [roadmap/machines.md](roadmap/machines.md) |
| Coverage and reuse | [roadmap/coverage.md](roadmap/coverage.md) |

## Documentation and repository

- **The guide** ([#585](https://github.com/cslib-community/cslib-frontier/issues/585)): A chapter per area, including Foundations (bit strings, Fourier analysis, PMF and `ProbComp`, codes), proof complexity, descriptive complexity, and Word RAM and algorithms, reusing checked examples.
- **Archive `complexitylib-v1`:** Archive the repository once its remaining work is dispositioned.
