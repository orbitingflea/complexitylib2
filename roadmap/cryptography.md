# Roadmap: Cryptography

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

### Cryptographic landmarks

- **Completeness of oblivious transfer** ([#1212](https://github.com/cslib-community/cslib-frontier/issues/1212)): In the ideal OT-hybrid model, every polynomial-time multiparty functionality admits a protocol secure against static malicious corruptions, with real/ideal simulation and abort, under the standard communication assumptions.
  The route needs ideal commitment realization from OT with efficient two-sided simulation, composition, a malicious compiler and MPC simulation.
- **Regev's worst-case to average-case reduction** ([#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)): For suitable `q` and Gaussian noise rate `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`.
  The noise law, modulus restrictions and quantum reduction are part of the theorem.
  Its foundations are [#2573](https://github.com/cslib-community/cslib-frontier/issues/2573), [#2592](https://github.com/cslib-community/cslib-frontier/issues/2592), [#2608](https://github.com/cslib-community/cslib-frontier/issues/2608), [#2624](https://github.com/cslib-community/cslib-frontier/issues/2624), [#2646](https://github.com/cslib-community/cslib-frontier/issues/2646), [#2659](https://github.com/cslib-community/cslib-frontier/issues/2659), [#2681](https://github.com/cslib-community/cslib-frontier/issues/2681), [#2707](https://github.com/cslib-community/cslib-frontier/issues/2707), [#2734](https://github.com/cslib-community/cslib-frontier/issues/2734), [#2766](https://github.com/cslib-community/cslib-frontier/issues/2766) and, for Lemma 3.11, [#2767](https://github.com/cslib-community/cslib-frontier/issues/2767).
- **Kilian's succinct arguments** ([#999](https://github.com/cslib-community/cslib-frontier/issues/999)): If collision-resistant hash families exist, every language in NP has an interactive argument with polylogarithmic communication, by committing to a PCP with Merkle trees; Micali's CS proofs and the BCS transform give the random-oracle versions.
  The target needs an honest prover efficient from an arbitrary NP witness, with the verifier's runtime and message truncation accounted for.

### Modern fully homomorphic encryption

Develop these in reviewable milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions where their hypotheses match.
The [pre-rewrite FHE section](https://github.com/cslib-community/cslib-frontier/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities) maps the schemes to current libraries and workloads.

- **Gentry's exact loss and running time** ([#2585](https://github.com/cslib-community/cslib-frontier/issues/2585), [#2722](https://github.com/cslib-community/cslib-frontier/issues/2722)): For Gentry's bootstrapping instantiated with GSW ([#486](https://github.com/cslib-community/cslib-frontier/issues/486), [#1104](https://github.com/cslib-community/cslib-frontier/issues/1104)), prove his exact concrete-security loss and the `poly(ℓ, d)` running-time clause of his Theorem 4.
  This includes the literal source loss mapping, a multiplicative comparison of primitive costs with adversary runtime, and the complete modular-game time and space assembly with prepared-metadata accounting.

1. **Ring arithmetic and RLWE**: Natively certify ring operations over `(Z/qZ)[X]/(X^d + 1)`, RNS/CRT conversions, rounding and modulus switching with error bounds and parity-preserving variants, and negacyclic NTT multiplication.
   Define the RLWE secret and error laws and experiment separately, since an ordinary-LWE reduction does not give them.
   For Module-LWE encryption, add native encryption, seed codecs and small-secret security.
2. **FHEW/TFHE programmable bootstrapping** ([Ducas–Micciancio](https://eprint.iacr.org/2014/816); [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870)): Prove the bootstrap decrypts to `f(m)` with its noise, failure, width and runtime bounds, under negacyclic lookup restrictions and torus representations.
   Floating-point FFTs need rounding-error proofs.
   Then add [Lee et al.'s smaller-key methods](https://eprint.iacr.org/2022/198) and batched variants with exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV** ([Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277); [Fan–Vercauteren](https://eprint.iacr.org/2012/144)): Slot encoding, multiplication, relinearization, rotations and level management, with leveled evaluation before a separately proved refresh.
   Equality modulo the plaintext modulus differs from ordinary integer equality, which needs a range bound.
4. **Approximate packed CKKS and its bootstrap** ([Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421)): An explicit approximate-correctness interface and a norm bound on decoded error covering rescaling, rounding, key switching and rotations.
5. **Scheme switching and threshold variants**: Explicit range and precision contracts, evaluation-key assumptions, corruption thresholds, interaction, robustness and decryption-query access, distinguishing honest-but-curious from malicious security.

For each scheme, prove chosen-plaintext security for the actual algorithms and public evaluation keys; keep LWE/RLWE, circular/KDM assumptions and attack-cost estimates distinct; introduce a decryption-failure game when correctness is not perfect; and require nonvacuous parameter families and full-input native runtime.

### Public-key, lattice and symmetric constructions ([#640](https://github.com/cslib-community/cslib-frontier/issues/640))

- **Sigma protocols and Fiat–Shamir** ([#581](https://github.com/cslib-community/cslib-frontier/issues/581)): Extend random-oracle EUF-CMA security of Schnorr signatures under discrete log, proved for fixed group families of polynomial description length (one description per security parameter, given to the reduction, with no computability requirement), to random group setups, and certify the generic Fiat–Shamir forking reduction for other Sigma protocols.
  Identification and eavesdropping security do not suffice.
  Its components are [#2672](https://github.com/cslib-community/cslib-frontier/issues/2672), [#2684](https://github.com/cslib-community/cslib-frontier/issues/2684), [#2696](https://github.com/cslib-community/cslib-frontier/issues/2696), [#2708](https://github.com/cslib-community/cslib-frontier/issues/2708), [#2724](https://github.com/cslib-community/cslib-frontier/issues/2724), [#2774](https://github.com/cslib-community/cslib-frontier/issues/2774), and forger replay in [#2579](https://github.com/cslib-community/cslib-frontier/issues/2579), [#2636](https://github.com/cslib-community/cslib-frontier/issues/2636) and [#2652](https://github.com/cslib-community/cslib-frontier/issues/2652).
- **Lattice signatures from SIS**: Prove random-oracle EUF-CMA security of Lyubashevsky's signatures (2009, 2012) from SIS by a native reduction that receives only `A`, with an efficient secret-free simulator and a security parameter family.
  The route covers forking ([#2620](https://github.com/cslib-community/cslib-frontier/issues/2620)), witness invariance ([#2642](https://github.com/cslib-community/cslib-frontier/issues/2642)), the ROM bridge ([#2661](https://github.com/cslib-community/cslib-frontier/issues/2661)), cache-hit bounds ([#2712](https://github.com/cslib-community/cslib-frontier/issues/2712)), oracle programming ([#2750](https://github.com/cslib-community/cslib-frontier/issues/2750)) and visible signing simulation ([#2788](https://github.com/cslib-community/cslib-frontier/issues/2788), [#2798](https://github.com/cslib-community/cslib-frontier/issues/2798)).
- **Lattice identification and Dilithium-style signatures**: Prove identification security under SIS, and the security of Dilithium-style signature schemes over module SIS and module LWE, as theory.
- **Hybrid encryption** ([#2749](https://github.com/cslib-community/cslib-frontier/issues/2749)): Extend adaptive CCA security of KEM–DEM hybrid encryption beyond the `n`-bit-message bound of Boneh–Shoup Exercise 12.5(a) ([#2725](https://github.com/cslib-community/cslib-frontier/issues/2725)) to arbitrary message spaces (unrestricted `WordINDCCA2`), prechallenge KEM queries and multiple encapsulation challenges.
- **Paillier encryption and composite residuosity**: Construct native balanced-modulus generation for Paillier encryption and instantiate its IND-CPA security under Decisional Composite Residuosity (Katz–Lindell Theorem 15.13) with that generator.
  The homomorphic property of Definition 15.14 for the word algorithms needs an exact or statistical-closeness formulation, since its exact distributional condition fails for the implemented sampler.
- **Goldwasser–Micali encryption** ([#5293](https://github.com/cslib-community/cslib-frontier/issues/5293)): Prove IND-CPA security of bitwise multi-bit Goldwasser–Micali encryption over Blum moduli from quadratic residuosity alone, for the actual word algorithms.
  Do the same for the textbook key generator, which samples the public nonresidue uniformly from `QNR_N^{+1}` using the factorization, without assuming its keys indistinguishable from an ideal law.
- **Garbled circuits and Yao's protocol** ([#3236](https://github.com/cslib-community/cslib-frontier/issues/3236)): Prove exact correctness and concrete simulation privacy of point-and-permute garbling for arbitrary-basis circuits, with privacy bounded by the sum of `n + size` PRF advantages.
  Prove semi-honest security of Yao's two-party protocol, with oblivious transfer realized by a protocol through an advantage-preserving composition theorem instead of an ideal batched OT oracle, and an asymptotic PPT statement from a word-level pseudorandom function.
  Extensions are output to both parties, and polynomial-time free-XOR and half-gates privacy.
- **Reusable fuzzy extractors from LWE**: Prove weak reusability of the common-matrix Fuller–Meng–Reyzin scheme (Apon–Cho–Eldefrawy–Katz Theorem 1) and strong reusability of their Section 5 scheme from `DecisionLWEWithErrors`.
  This needs an adversary class in the reuse experiments, efficiency certificates for `commonMatrixSimulator`, `encryptRealReduction` and `encryptIdealReduction`, and, for i.i.d. errors, `decisionLWE_iff_decisionLWEWithErrors`.
- **Universal one-way hashing from inaccessible entropy**: Prove the Haitner–Holenstein–Reingold–Vadhan–Wee construction of target-collision-resistant hash families from any one-way function as the source states it: inaccessible entropy against adversary-dependent accessible sets (Definition 3.9, [#4819](https://github.com/cslib-community/cslib-frontier/issues/4819)), the `d · log n / n` gap of Theorem 4.5 ([#4820](https://github.com/cslib-community/cslib-frontier/issues/4820)), and the `O(|y| log t)` compact keys of Lemma 5.7 ([#4821](https://github.com/cslib-community/cslib-frontier/issues/4821)).
- **General**: Reusable adaptive reductions, public-key encryption, universal-instance zero knowledge, hard-core predicates and hardness amplification, and connections to learning and average-case hardness.

### Zero-knowledge proof systems toward libzk ([#643](https://github.com/cslib-community/cslib-frontier/issues/643))

The libzk components are listed in build order, ending with libzk's compositional structure.

- **Public-coin to IP bridge**: Map public-coin protocols into IP with a uniform word verifier and adversarial message decoding.
- **Composition and round-by-round knowledge soundness**: Parallel and AND/OR composition of protocols and relations, with round-by-round knowledge soundness preserved under sequential, parallel and OR composition.
- **Oracle statements**: Let a later phase query an earlier phase's oracle message (virtual output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds.
- **Efficient simulators and auxiliary-input zero knowledge**: Efficiency-certified simulators and extractors, and auxiliary-input zero knowledge on the interactive core.
- **Polynomial commitments and Ligero**: Polynomial commitment and evaluation-query reductions, and the Ligero IOP.
- **BCS transform**: Compile IOPs into non-interactive arguments in the random-oracle model with soundness and knowledge-soundness bounds, machine-level verifier and extractor runtime, a polynomial-time encoding of NP witnesses into IOPs, and zero knowledge.
- **VOLE constraint reductions and VOLE-in-the-head**: Prove full zero-knowledge security of VOLE-based proofs for the arithmetic-circuit relation `∃ w, C.eval (x ++ w) = y`, with fresh-session amplification, scalar-challenge batching, growing fields, adversarial setup and scheduling, then VOLE-in-the-head.
  This includes a native circuit prover/verifier certificate with honest-sender realization ([#2765](https://github.com/cslib-community/cslib-frontier/issues/2765)) and raw-bit adversarial transport ([#2744](https://github.com/cslib-community/cslib-frontier/issues/2744)).
- **libzk composition**: Express libzk's compositional structure as a composition of these components, without ciphersuites.

### Private information retrieval ([#3251](https://github.com/cslib-community/cslib-frontier/issues/3251))

Information-theoretic private information retrieval, following Chor–Goldreich–Kushilevitz–Sudan (CGKS).

- **Information-theoretic PIR** ([#3451](https://github.com/cslib-community/cslib-frontier/issues/3451)): one-round schemes with perfect correctness and single-server privacy: subcube schemes with the rows transformation, covering-code schemes and schemes from perfectly smooth decoders.
  The covering-code schemes of CGKS Section 3.3 include radius-`2` codes, the other dimensions of Figure 1, the asymptotic lower estimate and server time, and take variable-length answers so that unbalanced covers meet CGKS Theorem 1 exactly.
  Also `t`-private schemes against coalitions, block retrieval and the converse from schemes to smooth codes (Katz–Trevisan).
- **PIR lower bounds** ([#3426](https://github.com/cslib-community/cslib-frontier/issues/3426)): the single-server bound with and without interaction, the two-server linear-summation bound with its tight even-set scheme (CGKS Section 5), and lower bounds for general two-server schemes.
- **Plinko privacy and bounds** ([#5736](https://github.com/cslib-community/cslib-frontier/issues/5736)): Prove privacy of the full `plinkoScheme` (the hint-refresh argument and a reduction to forward iPRF security), the security half of Theorem 4.4 with pseudorandom multinomial samplers, and the Theorem 5.3 bounds, including the hint-load and failure-probability estimates.

### Concurrent and quantum security

- **NIST post-quantum portfolio** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987); machine witnesses [#5285](https://github.com/cslib-community/cslib-frontier/issues/5285)): Faithful protocols and exact concrete/asymptotic quantum reductions for ML-KEM/DSA, SLH/FN-DSA, HQC and active signatures.
  Concrete endpoints charge constructed-program size and online time, space, randomness, queries and circuits; asymptotic reductions certify uniform polynomial composition.
  Preserve sampling, abort, transform, failure, controller-layout/relocation and evolving-claim obligations; operational QPPT/QROM security remains open.
- **FAEST security**: Parsing is [#5214](https://github.com/cslib-community/cslib-frontier/issues/5214); row-to-VOLE is [#5246](https://github.com/cslib-community/cslib-frontier/issues/5246). BAVC, QuickSilver, correctness and ROM/QROM security remain.
- **HQC security** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Connect the finite Theorem 6.3 game hops to classical ([#5290](https://github.com/cslib-community/cslib-frontier/issues/5290)) and native ([#5281](https://github.com/cslib-community/cslib-frontier/issues/5281)) DQCSD assumptions with machine and circuit resource certificates.
  Then complete the sampler/seed model, numerical DFR, the published Theorem 6.4 salted Fujisaki–Okamoto/ROM and KEM endpoint ([#5279](https://github.com/cslib-community/cslib-frontier/issues/5279)), and the separate QROM upgrade ([#5280](https://github.com/cslib-community/cslib-frontier/issues/5280)).
- **SQIsign foundations** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Extend its `B_{p,∞}` presentation with maximal orders and ideals, finite-field and elliptic-curve arithmetic, isogenies and Deuring, protocol algorithms, failure analysis, distribution switches, assumptions and security reductions.

- **SDitH foundations**: [#5212](https://github.com/cslib-community/cslib-frontier/issues/5212), [#5263](https://github.com/cslib-community/cslib-frontier/issues/5263) and [#5542](https://github.com/cslib-community/cslib-frontier/issues/5542) are bounded binary-RSD, `TweakSalt` and two-child `ExpandSeed` milestones. Algorithm 6's byte PRG, the full GGM/BAVC tree, the PIOP, commitments, grinding, signing/verification, hardness, machine costs, asymptotic family security and finite instantiated exact-constant bounds remain under [#4987](https://github.com/cslib-community/cslib-frontier/issues/4987).

- **Concurrent composition**: Extend the protocol semantics with environments, scheduling, session identifiers and concurrent executions, and prove a composition theorem with efficient simulators and explicit setup, corruption and communication assumptions.
  Then develop selected adaptive-corruption and non-malleability applications, alongside the static-malicious OT target.
- **Quantum-secure cryptography**: Define uniform quantum-efficient distinguishers and computational indistinguishability with quantum side information, and justify security reductions for concrete constructions in that model.
  Connect the quantum-computation and lattice tracks through these adversary models.
  Later targets include quantum oracle access, the quantum random-oracle model, and extraction or rewinding under their precise hypotheses.
