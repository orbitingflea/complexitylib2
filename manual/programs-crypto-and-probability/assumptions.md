# Assumptions inventory

A security theorem may assume named hardness assumptions: Prop-valued definitions documented as assumptions, such as `F.DDH setup`, `DecisionLWE …` or `OneWay f`, including a security notion of a component that the caller supplies ([AGENTS.md, Security theorems](../../AGENTS.md#security-theorems)). This page lists each such assumption that the check below finds a theorem in `Cslib.Crypto` taking, and the hardness assumptions the library defines. It is not complete: the check misses some assumptions, and the paragraphs on its limits below name the known ones. For each listed assumption, the page says where the definition comes from:

- **standard**: a cited source states the assumption, and the docstring cites that source definition. The row gives the bibliography key of [references.bib](../../references.bib) and the locator. *Deviations or relation* names every material difference from the source, such as an arbitrary setup law where the source has an efficient parameter generator. A deviation that strengthens the assumption (more adversaries, more information for them, a dropped restriction that the source relies on) makes it novel, unless a cited source states that form or the library proves it from the standard one.
- **novel**: no cited source states the assumption. Its docstring says that it is novel to this library, and *Deviations or relation* says how it relates to standard assumptions (it follows from one, implies one, or neither) and why it is plausible. A novel assumption may support a result presented as original. A theorem that rests on it names it, and is never presented as a cited result: that would be a stand-in under [Faithful headlines](../../AGENTS.md#faithful-headlines) rule 2.
- **vocabulary**: a generic notion parameterized by the objects whose security it states (games, ensembles, an adversary predicate, a bound), such as `Game.Indistinguishable` or `ComputationallyIndistinguishable`. It becomes an assumption only through the instance that a theorem supplies, and review checks that instance under a cited headline. A primitive's or problem's own security notion is never vocabulary, even in a concrete form against a caller's adversary class and bound, as `PRG.Generator.Secure` is.

A row of any status says "locator not verified" until someone has read its locator at the source. A pull request removes the phrase only when its body records that check (the source's version or URL and what was read there) and its reviewer confirms it at the source. A row that says "status pending" has an open question about its status, named in the row; until it is settled, the assumption does not count as the source's under a cited headline. The Boneh–Shoup locators without that phrase were read in Version 0.6 of the book (January 2023), the Regev locator in the author's 2009 version of the paper, and the Kyber and Dilithium locators in versions 3.02 and 3.1 of their specifications. The pull request that removed the phrase from a row ([#5585](https://github.com/cslib-community/cslib-frontier/pull/5585) for the first rows) records in its description what was read, and its reviewers confirmed it.

*Nonvacuity* links a test that shows the assumption fails for an insecure instance (for example a fixed group, a zero noise law or a constant function), where the library has one.

[check_hardness_assumptions.py](../../scripts/check_hardness_assumptions.py) reads the built library after `lake build CslibFrontier`. It finds every premise of a public Crypto theorem headed by a Prop-valued declaration whose definition mentions negligibility, an advantage or indistinguishability, whatever the declaration's own name, and checks it against this page. An unregistered assumption fails. So does a standard assumption whose docstring cites none of its row's keys, a novel assumption whose docstring does not say "novel to this library", a "locator not verified" in a row of any status, and a theorem resting on a novel assumption that does not name it, or whose docstring presents a cited result (it cites a key, or its first sentence says "theorem" or opens with a bold title) without its first sentence saying "step" or "helper". The existing gaps are recorded, each with a justification, in [hardness_assumptions_baseline.json](../../scripts/hardness_assumptions_baseline.json), which may only shrink. Pull requests and merge groups enforce the check. `python3 scripts/check_hardness_assumptions.py --list` prints the theorems that rest on each assumption. The audit behind this page is [#5578](https://github.com/cslib-community/cslib-frontier/issues/5578).

The check does not judge whether a definition matches its source, whether a locator is right, or whether a theorem that claims a cited result rests on the assumption that the source uses, with the source's instance. It does not see a cited result that a docstring names without a bibliography key, the word "theorem" or a bold title in its first sentence, nor one that only a theorem's name claims. The step test is syntactic too: an original result on a novel assumption, which the rule allows, is flagged when its docstring cites a key, or its first sentence says "theorem" or opens with a bold title, and then passes only through a justified baseline entry. Review covers all of this ([Review cycle](../../AGENTS.md#review-cycle)).

The reader also misses two kinds of assumption. One is a premise written inline, such as a hypothesis `∀ A, Negligible (advantage A)`, which no named declaration heads. The other is a Prop-valued definition that reaches no security atom (`Negligible`, a constant named like an advantage, or one whose name contains `Indistinguishable`) through Prop-valued declarations within five levels: a bound on a quantity not named like an advantage, such as a success probability or an agreement fraction; an advantage behind a helper that is not Prop-valued; or a security atom reached only through a chain of more than five Prop-valued declarations. Such assumptions are not on this page, and a row for one fails as naming no named assumption. The known cases ([#5578](https://github.com/cslib-community/cslib-frontier/issues/5578) finding 9) are:

- `Cslib.Complexity.MildlyHardOnAverage` and `Cslib.Complexity.MildlyHardOnAverageENat`, which the Liu–Pass converse in `OneWay/LiuPassConverse.lean` assumes (`Cslib.Crypto.exists_oneWay_of_mildlyHardOnAverage_timeBoundedNat` and its companions);
- `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGap` and `Cslib.Crypto.Pseudoentropy.SamplablePair.HasGapWithAdvice`, assumed throughout `Pseudoentropy/`;
- `Cslib.Circuits.Boolean.IsAverageCaseHard`, which the Nisan–Wigderson bound `Cslib.Crypto.PRG.NisanWigderson.abs_card_div_sub_card_div_lt` assumes.

Registering them needs the reader to accept them first, which is a follow-up of #5578.

Names are relative to `Cslib.Crypto`.

## Group-based assumptions

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `PrimeOrderGroupFamily.DiscreteLog` | standard | [BonehShoup2023] Attack Game 10.4 and Definition 10.6, p. 409; asymptotic form with Definition 10.9, p. 413 | The setup law is any `ℕ → PMF F.Desc`; Boneh–Shoup's group parameters come from an efficient algorithm (Definition 10.9), so the assumption is the source's only for efficiently sampled setup laws. The adversary's time is polynomial in its input, including the encoded group parameters, whose length an efficient setup keeps polynomial in `n`. The adversary writes the exponent as a bit string, read modulo `q`. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_discreteLog_const` |
| `PrimeOrderGroupFamily.CDH` | standard | [BonehShoup2023] Attack Game 10.5 and Definition 10.7, pp. 409–410 | Any setup law, as for `DiscreteLog`. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_cdh_const` |
| `PrimeOrderGroupFamily.DDH` | standard | [BonehShoup2023] Attack Game 10.6 and Definition 10.8, pp. 410–411 | Any setup law, as for `DiscreteLog`. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_ddh_const` |
| `PrimeOrderGroupFamily.MultiDDH` | standard | [BonehShoup2023] Exercise 10.11 (Multi-DDH (I)), p. 426 | Proved from `DDH` (`DDH.multiDDH`). | — |
| `PrimeOrderGroupFamily.SingleSecretMultiDDH` | standard | [BonehShoup2023] Exercise 10.11 (Multi-DDH (I)), p. 426 | The case of one secret; proved from `DDH`. | — |
| `PrimeOrderGroupFamily.SecureKDF` | standard | [BonehShoup2023] Attack Game 11.3, p. 448, and Definition 11.5, p. 449 | Relative to the setup law of the group. | [DiffieHellman.lean](../../CslibFrontierTests/Crypto/DiffieHellman.lean) `not_secureKDF_constZeroKDF` |
| `PrimeOrderGroupFamily.LinearHashKDFConditions` | standard | [BonehShoup2023] Theorem 8.11 (leftover hash lemma), p. 334 | The statistical hypotheses under which the linear-hash KDF is a `SecureKDF`; not a hardness assumption. | — |

## Factoring-based assumptions

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `QuadraticResiduosityHard` | standard | [KatzLindell2020] Section 15.4.3 (locator not verified) | Any law on the primes; the ideal game samples nonresidues with Jacobi symbol `+1`. | — |
| `DCR` | standard | [KatzLindell2020] Definition 15.10 (locator not verified) | Balanced moduli from any law. | — |
| `FactoringHard` | standard | [KatzLindell2020] Section 9.2.3 (locator not verified) | Blum moduli only, drawn from any law on `BlumDesc` (`BlumGen`), which need not be efficiently samplable. | — |
| `RabinOneWay` | standard | [KatzLindell2020] Section 15.5.2 (locator not verified) | Blum moduli from any law on `BlumDesc`, which need not be efficiently samplable. The input is a uniform bit string twice as long as `N`, reduced modulo `N`, not a uniform unit. | — |
| `RSAOneWay` | standard | [BonehShoup2023] Attack Game 10.3 and Definition 10.5, pp. 404–405 | Keys from any law on `RSADesc` (`RSAGen`), which need not be efficiently samplable, in place of Boneh–Shoup's `RSAGen(ℓ, e)`. The challenge is uniform on `Fin N`, as `x ← Z_n` in the source. | [RSALeastSignificantBit.lean](../../CslibFrontierTests/Crypto/RSALeastSignificantBit.lean) `not_rsaOneWay_desc33` |

## Lattice and code assumptions

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `DecisionLWE` | standard | [Regev2009] Section 2 (`LWE_{p,χ}`) and Section 4 (decision variant) | Modulus `2 ^ w` only; any noise law; uniform classical distinguishers. | [SigmaLWECCANonvacuity.lean](../../CslibFrontierTests/Crypto/SigmaLWECCANonvacuity.lean) `not_decisionLWE_zeroNoise` |
| `DecisionLWEWithErrors` | standard | [FullerMengReyzin2020] Section 4 (locator not verified) | Status pending ([#5578](https://github.com/cslib-community/cslib-frontier/issues/5578) finding 5): whether the source assumes this form is not yet checked. A joint, possibly correlated, error law; `DecisionLWE` is the product case. | — |
| `DecisionModuleLWE` | standard | [DucasEtAl2018] (locator not verified) | `DecisionModuleLWEWith` with a uniform secret and independent errors; ML-KEM and ML-DSA need the short secrets that `DecisionModuleLWEWith` admits (#5293). | [ModuleSIS.lean](../../CslibFrontierTests/Crypto/ModuleSIS.lean) `not_decisionModuleLWE_zeroNoise` |
| `DecisionModuleLWEWith` | standard | [AvanziEtAl2021] Section 4.3, p. 19, and [BaiEtAl2021Dilithium] Section 6.1, p. 23 | Asymptotic: every uniform classical strict PPT distinguisher has negligible advantage over the family, where the sources define concrete advantages at fixed parameters (`Adv^mlwe_{m,k,η}`, `Adv^MLWE_{m,k,D}`). Any secret and error laws, where Kyber draws both from the centered binomial law `β_η` and Dilithium both from one law `D`; under a cited headline, review checks the laws that a theorem supplies. Meaningful only for a family whose parameters grow with `κ`. | [ModuleSIS.lean](../../CslibFrontierTests/Crypto/ModuleSIS.lean) `not_decisionModuleLWE_zeroNoise` |
| `SIS` | standard | [Ajtai1996] (locator not verified) | — | [ModuleSIS.lean](../../CslibFrontierTests/Crypto/ModuleSIS.lean) `not_sis_zeroRowSIS` |
| `ModuleSIS` | standard | [Lyubashevsky2012], [DucasEtAl2018] (locator not verified) | — | [ModuleSIS.lean](../../CslibFrontierTests/Crypto/ModuleSIS.lean) `not_moduleSIS_zeroRankModuleSIS` |
| `RingSIS` | standard | [Lyubashevsky2012] (locator not verified) | `ModuleSIS` at rank 1. | [ModuleSIS.lean](../../CslibFrontierTests/Crypto/ModuleSIS.lean) `not_ringSIS_boundAtModulus` |
| `HQC.NativeQuantumTwoDQCSDP` | standard | [HQC2026] Definitions 2.3.6–2.3.9, pp. 12–13 (locator not verified) | Native quantum tests without advice or a useful oracle. | [HQCDQCSD.lean](../../CslibFrontierTests/Crypto/HQCDQCSD.lean) `not_nativeQuantumTwoDQCSDP_fullWeight` |
| `HQC.NativeQuantumTwoDQCSDPWithin` | standard | [HQC2026] Definitions 2.3.6–2.3.9, pp. 12–13 (locator not verified) | Concrete form, with separate circuit resource budgets. | [HQCDQCSD.lean](../../CslibFrontierTests/Crypto/HQCDQCSD.lean) `not_nativeQuantumTwoDQCSDPWithin_fullWeight` |
| `HQC.NativeQuantumThreeDQCSDPT` | standard | [HQC2026] Definitions 2.3.6–2.3.9, pp. 12–13 (locator not verified) | Native quantum tests without advice or a useful oracle. | [HQCDQCSD.lean](../../CslibFrontierTests/Crypto/HQCDQCSD.lean) `not_nativeQuantumThreeDQCSDPT_fullWeight` |
| `HQC.NativeQuantumThreeDQCSDPTWithin` | standard | [HQC2026] Definitions 2.3.6–2.3.9, pp. 12–13 (locator not verified) | Concrete form, with separate circuit resource budgets. | [HQCDQCSD.lean](../../CslibFrontierTests/Crypto/HQCDQCSD.lean) `not_nativeQuantumThreeDQCSDPTWithin_fullWeight` |

## Other assumptions

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `Encryption.CircularSecure` | standard | [Gentry2009] Section 2 (locator not verified) | One-key circular security: the bitwise encryption of the secret key, jointly with the public key, against encryptions of zeros. | [FixedKeySecurity.lean](../../CslibFrontierTests/Crypto/FixedKeySecurity.lean) `not_circularSecure_leak` |
| `GMW.AdvicePRG` | novel | — | Follows from `NonuniformPRG` (`NonuniformPRG.advicePRG`), hence from `NonuniformOneWay`; not known to follow from a uniform PRG. A generator at seed length `n + 7` against tests that also read polynomially bounded instance, witness and auxiliary-input families. | [Nonuniform.lean](../../CslibFrontierTests/Crypto/Nonuniform.lean) `not_advicePRG_cons_false` |
| `Garbling.MixedModulus.MixedModulusCCR` | novel | [BallMalkinRosulek2016] Definition 1 (locator not verified) is the closest source. | Stronger than that definition: its relaxed legality condition admits every adversary legal there, and more (module docstring). | [GarblingBMR16.lean](../../CslibFrontierTests/Crypto/GarblingBMR16.lean) `not_mixedModulusCCR_zeroH` |
| `PRG.IsSubexponentiallySecure` | standard | [RazborovRudich1997] Section 4 (locator not verified) | Exponents rounded to integers. | [NaturalProofs.lean](../../CslibFrontierTests/NaturalProofs.lean) `not_isSubexponentiallySecure_zeroPad` |
| `PRG.IsExponentiallySecure` | standard | [RazborovRudich1997] Section 4 (locator not verified) | — | [NaturalProofs.lean](../../CslibFrontierTests/NaturalProofs.lean) `not_isExponentiallySecure_const` |
| `NonuniformOneWay` | standard | [Goldreich2001] Section 2.2 (locator not verified) | Uniform strict PPT inverters with polynomially bounded advice, whose length is charged to their clock. | [Nonuniform.lean](../../CslibFrontierTests/Crypto/Nonuniform.lean) |
| `NonuniformPRG` | standard | [Goldreich2001] Section 3.2 (locator not verified) | Uniform strict PPT tests with polynomially bounded advice, as for `NonuniformOneWay`. | [Nonuniform.lean](../../CslibFrontierTests/Crypto/Nonuniform.lean) |
| `InversionHardWithAdvice` | standard | [Goldreich2001] Section 2.2 (locator not verified) | One fixed advice family. | [Nonuniform.lean](../../CslibFrontierTests/Crypto/Nonuniform.lean) |
| `WeakOneWay` | standard | [LiuPass2020] Definition 2.2 (locator not verified) | — | [WeakOneWay.lean](../../CslibFrontierTests/WeakOneWay.lean) |
| `WeakOneWayAt` | standard | [LiuPass2020] Definition 2.2 (locator not verified) | — | — |
| `CondEPPRG` | standard | [LiuPass2020] Definition 5.1 (locator not verified) | — | — |
| `BooleanPRF` | standard | [FanLiYang2022] Definitions 4.4–4.5 (locator not verified) | No efficiency condition, as in the source; the uniform ensemble satisfies it. | — |

## One-way functions, generators and pseudorandom functions

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `OneWay` | standard | [Goldreich2001] Definition 2.2.1 (locator not verified) | Uniform strict PPT inverters; any preimage wins. | [ComputationalCrypto.lean](../../CslibFrontierTests/ComputationalCrypto.lean) |
| `OneWayPermutation` | standard | [Goldreich2001] Section 2.4 (locator not verified) | Length-preserving permutations. | — |
| `HardCore` | standard | [Goldreich2001] Definition 2.5.1 (locator not verified) | — | [ComputationalCrypto.lean](../../CslibFrontierTests/ComputationalCrypto.lean) |
| `PseudorandomGenerator` | standard | [BonehShoup2023] Attack Game 3.1 and Definition 3.1, pp. 46–47 | Deterministic polynomial-time evaluation and strict expansion are part of the notion. | [ComputationalCrypto.lean](../../CslibFrontierTests/ComputationalCrypto.lean) |
| `PRG.Generator.Secure` | standard | [BonehShoup2023] Attack Game 3.1 and Definition 3.1, pp. 46–47 | CSLib's concrete form for one generator on finite seed and output types: advantage at most `ε` for every adversary in a class `Admissible` that the caller supplies, where Definition 3.1 asks for negligible advantage against every efficient adversary. Neither efficiency nor expansion of the generator is part of the notion. Under a cited headline, review checks the class and bound that a theorem supplies. | — |
| `PRG.Generator.Unpredictable` | standard | [BonehShoup2023] Attack Game 3.2 and Definition 3.3, p. 64 | Concrete, against a predictor class and bound that the caller supplies, as for `PRG.Generator.Secure`. Each predictor has a fixed position, where the adversary of Attack Game 3.2 chooses it; a bound at every position also bounds a predictor that chooses its position at random. | — |
| `PseudorandomFunction` | standard | [BonehShoup2023] Attack Game 4.2 and Definition 4.2, pp. 132–133 | Adaptive uniform oracle tests; length-preserving families. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_pseudorandomFunction_zeroFamily` |
| `WeakPseudorandomFunction` | standard | [KatzLindell2020] Exercise 3.28 (locator not verified) | — | — |
| `BlockCipher.PRP` | standard | [BonehShoup2023] Definition 4.1, p. 98 | Read asymptotically, as in Section 4.1.5. | — |
| `BlockCipher.StrongPRP` | standard | [BonehShoup2023] Section 4.1.3, pp. 101–102, and Exercise 4.9, p. 169 | — | — |

## Hashing

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `CollisionResistantForOn` | standard | [BonehShoup2023] Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291 | The setup law need not be efficiently samplable; inputs are restricted to `valid`. | — |
| `CollisionResistantFor` | standard | [BonehShoup2023] Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291 | `CollisionResistantForOn` on all inputs. | [CCA.lean](../../CslibFrontierTests/Crypto/CCA.lean) `not_collisionResistantFor_constZModHash` |
| `CollisionResistantOn` | standard | [BonehShoup2023] Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291 | Keyed by uniform `n`-bit keys. | — |
| `CollisionResistant` | standard | [BonehShoup2023] Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291 | On all bit strings. | [MerkleDamgard.lean](../../CslibFrontierTests/Crypto/MerkleDamgard.lean) `not_collisionResistant_constHash` |
| `CompressionFamily` | standard | [BonehShoup2023] Section 8.2 (locator not verified) | `2n → n` compression under `n`-bit keys, evaluated in polynomial time. | — |
| `HashFamily` | standard | [BonehShoup2023] Attack Game 8.1 and Definitions 8.1–8.2, pp. 290–291 | Arbitrary-length messages, `n`-bit keys and digests, evaluated in polynomial time. | — |
| `TargetCollisionResistantOn` | standard | [BonehShoup2023] Attack Game 8.5 and Definition 8.7, pp. 337–338 | Uniform `keyLen n`-bit keys; inputs are restricted to `valid`. | [NaorYungUOWHF.lean](../../CslibFrontierTests/Crypto/NaorYungUOWHF.lean) `not_targetCollisionResistantOn_naorYungStep_id` |
| `TargetCollisionResistant` | standard | [BonehShoup2023] Attack Game 8.5 and Definition 8.7, pp. 337–338 | On all bit strings. | — |
| `KeyedHashFamily.TargetCollisionResistant` | standard | [BonehShoup2023] Attack Game 8.5 and Definition 8.7, pp. 337–338 | On all bit strings. | — |
| `KeyedCompressionFamily.TargetCollisionResistant` | standard | [BonehShoup2023] Attack Game 8.5 and Definition 8.7, pp. 337–338 | On `2n`-bit inputs. | [TargetCollisionResistant.lean](../../CslibFrontierTests/Crypto/TargetCollisionResistant.lean) `not_targetCollisionResistant_xorKeyedCompression` |
| `MerklePositionBinding` | standard | [BonehShoup2023] Definition 8.4, p. 324 | Keyed by a uniform `n`-bit key, where the source's scheme (Attack Game 8.2) is unkeyed with a fixed number of leaves. The adversary chooses the depth: both openings are checked at the depth of the first path. Positions written in unary. | — |

## Encryption

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `Encryption.INDCPA` | standard | [BonehShoup2023] Attack Game 11.1 and Definition 11.2, pp. 436–437 | One challenge; bit messages. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_indcpa_plaintext` |
| `Encryption.INDCPAOf` | standard | [BonehShoup2023] Attack Game 11.1 and Definition 11.2, pp. 436–437 | One challenge; every challenge pair admissible. | — |
| `Encryption.INDCPAOn` | standard | [BonehShoup2023] Attack Game 11.1 and Definition 11.2, pp. 436–437 | One challenge; an admissibility predicate. | — |
| `Encryption.WordINDCPA` | standard | [BonehShoup2023] Attack Game 11.1 and Definition 11.2, pp. 436–437 | One challenge; equal-length messages. | — |
| `Encryption.INDCCA2` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.2, pp. 467–468 | 1CCA; bit messages. | [AssumptionNonvacuity.lean](../../CslibFrontierTests/Crypto/AssumptionNonvacuity.lean) `not_indcca2_plaintext` |
| `Encryption.INDCCA2Of` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.2, pp. 467–468 | 1CCA; every challenge pair admissible. | — |
| `Encryption.INDCCA2On` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.2, pp. 467–468 | 1CCA; an admissibility predicate. | — |
| `Encryption.WordINDCCA2` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.2, pp. 467–468 | 1CCA; equal-length messages. | — |
| `Encryption.INDCCA2Multi` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.1, pp. 467–468 | Challenges in one batch, not adaptively; bit messages. | — |
| `Encryption.INDCCA2MultiOf` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.1, pp. 467–468 | Challenges in one batch, not adaptively. | — |
| `Encryption.INDCCA2MultiOn` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.1, pp. 467–468 | Challenges in one batch, not adaptively. | — |
| `Encryption.WordINDCCA2Multi` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.1, pp. 467–468 | Challenges in one batch, not adaptively; equal-length messages. | — |
| `Encryption.INDCCA2InterleavedOn` | standard | [BonehShoup2023] Attack Game 12.1 and Definition 12.1, pp. 467–468 | Fully adaptive, round-structured adversaries. | — |
| `Encryption.KEMINDCPA` | standard | [BonehShoup2023] Exercise 11.9 (locator not verified) | Uniform bit-word keys; no correctness or efficient sampling bundled. | — |
| `Encryption.DEMOneTimeKeyINDCPAOn` | standard | [BonehShoup2023] Attack Game 2.1 and Definition 2.2, p. 16 | Key length `keyLen n`; an admissibility predicate. | — |
| `Encryption.DEMOneTimeKeyINDCPAOf` | standard | [BonehShoup2023] Attack Game 2.1 and Definition 2.2, p. 16 | Every challenge pair admissible. | — |
| `Encryption.DEMOneTimeKeyWordINDCPA` | standard | [BonehShoup2023] Attack Game 2.1 and Definition 2.2, p. 16 | Equal-length messages. | — |
| `Encryption.DEMOneTimeINDCPAOn` | standard | [BonehShoup2023] Attack Game 2.1 and Definition 2.2, p. 16 | `n`-bit keys; an admissibility predicate. | — |
| `Encryption.DEMOneTimeINDCPAOf` | standard | [BonehShoup2023] Attack Game 2.1 and Definition 2.2, p. 16 | `n`-bit keys; every challenge pair admissible. | — |
| `SymmetricCipher.INDCPA` | standard | [BonehShoup2023] Attack Game 5.2 and Definition 5.2, pp. 181–182 | Both messages of a query have exactly `n` bits; the oracle answers other queries with `[]`. | — |
| `SymmetricCipher.OneTimeINDCPA` | standard | [BonehShoup2023] Definition 2.2, p. 16, and Definition 9.4, p. 360 | — | — |
| `SymmetricCipher.CiphertextIntegrity` | standard | [BonehShoup2023] Attack Game 9.1 and Definition 9.1, pp. 358–359 | — | — |
| `SymmetricCipher.OneTimeCiphertextIntegrity` | standard | [BonehShoup2023] Definition 9.3, p. 360 | — | — |
| `SymmetricCipher.AuthenticatedEncryption` | standard | [BonehShoup2023] Definition 9.2, p. 359 | — | — |
| `SymmetricCipher.OneTimeAuthenticatedEncryption` | standard | [BonehShoup2023] Definition 9.4, p. 360 | — | — |
| `SymmetricCipher.INDCCA` | standard | [BonehShoup2023] Attack Game 9.2 and Definition 9.5, p. 362 | — | — |
| `SymmetricCipher.OneTimeINDCCA` | standard | [BonehShoup2023] Definition 9.6, p. 363 | — | — |
| `SymmetricCipher.EncForge` | standard | [KatzLindell2020] Definition 5.2 (locator not verified) | — | — |
| `SymmetricCipher.RealIdealAE` | standard | [KatzLindell2020] Definition 5.4 (locator not verified) | — | — |
| `Protocols.FujisakiOkamoto.WordPKE.INDCPA` | standard | [HofheinzHoevelmannsKiltz2017] Definition 2.2 (locator not verified) | Challenge messages in the scheme's message space. | — |

## Authentication and signatures

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `MACScheme.EUFCMA` | standard | [BonehShoup2023] Attack Game 6.1 and Definition 6.2, pp. 218–219 | A forgery must be on a fresh message, which is weaker than Boneh–Shoup's fresh pair. | — |
| `MACScheme.SUFCMA` | standard | [BonehShoup2023] Attack Game 6.1 and Definition 6.2, pp. 218–219 | — | — |
| `MACScheme.OneTimeEUFCMA` | standard | [BonehShoup2023] Attack Game 6.1 and Definition 6.2, pp. 218–219 | One signing query; fresh message. | — |
| `MACScheme.OneTimeSUFCMA` | standard | [BonehShoup2023] Attack Game 6.1 and Section 7.6 (locator not verified) | One signing query. | — |
| `MACScheme.BlockwiseEUFCMA` | standard | [KatzLindell2020] Construction 4.7 and Theorem 4.8 (locator not verified) | — | — |
| `NonceMACScheme.SUFCMA` | standard | [BonehShoup2023] Attack Game 7.4, p. 274 | — | — |
| `NonceMACScheme.EUFCMA` | standard | [BonehShoup2023] Attack Game 7.4, p. 274 | Fresh message. | — |
| `NonceMACScheme.CounterSUFCMA` | standard | [BonehShoup2023] Section 7.5 (locator not verified) | A counter as the nonce. | — |
| `SignatureScheme.EUFCMA` | standard | [BonehShoup2023] Attack Game 13.1 and Definition 13.2, pp. 529–530 | — | — |
| `SignatureScheme.OneTimeEUFCMA` | standard | [BonehShoup2023] Attack Game 13.1 and Definition 13.2, pp. 529–530 | One signing query. | — |
| `WordSignatureScheme.EUFCMA` | standard | [BonehShoup2023] Attack Game 13.1 and Definition 13.2, pp. 529–530 | Arbitrary-length messages. | — |
| `IndexedSignatureScheme.IndexedEUFCMA` | standard | [BonehShoup2023] Definition 14.6, p. 597 | Differences listed in the module docstring. | — |
| `IndexedSignatureScheme.CounterEUFCMA` | standard | [BonehShoup2023] Section 14.6.4, p. 602 | A counter as the nonce. | — |
| `Protocols.ROMSignature.EUFCMA` | standard | [BonehShoup2023] Attack Game 13.1, random-oracle version (locator not verified) | — | — |

## Zero knowledge, commitments and protocols

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `StatefulHiding` | standard | [Naor1991] (locator not verified) | A stateful receiver that chooses both bits. | — |
| `CommitmentScheme.StatisticalHiding` | standard | [BonehShoup2023] Section 8.12: the hiding experiment, p. 344, and unconditional hiding, p. 346 | The source names unconditional hiding in prose (statistically indistinguishable commitments), not in a numbered definition; Definition 8.8 is a secure (hiding and binding) scheme. Read here as the p. 344 experiment against every adversary: an unbounded `Encryption.WordAdversary` that sees the public parameters, drawn from a setup law `keyDist` (the source's scheme has none), and chooses the two messages. | — |
| `FuzzyExtractor.ComputationallySecureFor` | standard | [FullerMengReyzin2020] Definition 2.2, item 4 (locator not verified) | — | — |
| `ZKProof.NegligibleSoundness` | standard | [Goldreich2001] Section 4.2 (locator not verified) | A finite soundness error at every parameter. | — |
| `AuxiliaryInputZeroKnowledge` | standard | [Goldreich2001] Section 4.3.3, Definition 4.3.10 (locator not verified) | Uniform strict PPT verifiers and simulators; polynomially bounded families. | — |
| `ZKProof.AuxiliaryInputZeroKnowledge` | standard | [Goldreich2001] Section 4.3.3, Definition 4.3.10 (locator not verified) | As `AuxiliaryInputZeroKnowledge`, for a bundled proof system. | — |
| `UnboundedAuxiliaryInputZeroKnowledge` | standard | [Goldreich2001] Section 4.3.3, Definition 4.3.10 (locator not verified) | Auxiliary input of any length, read through a polynomial prefix. | — |
| `ZKProof.UnboundedAuxiliaryInputZeroKnowledge` | standard | [Goldreich2001] Section 4.3.3, Definition 4.3.10 (locator not verified) | As above, for a bundled proof system. | — |
| `GenerableZeroKnowledge` | standard | [Goldreich2001] Section 4.3 (locator not verified) | Polynomial-time generable families. | — |
| `Protocols.SigmaProtocol.ComputationalSpecialHVZK` | standard | [BonehShoup2023] Section 20.4.2 and Definition 20.6, p. 840 | An acceptance error `δ`. | — |
| `Protocols.UC.EmulatesWithin` | standard | [Canetti2020] Section 4 (locator not verified) | Concrete budgets and error. | — |
| `Protocols.UC.Emulates` | standard | [Canetti2020] Section 4 (locator not verified) | — | — |
| `Protocols.UC.Realizes` | standard | [Canetti2020] Section 4 (locator not verified) | — | — |
| `Protocols.UC.EmulatesDummyWithin` | standard | [Canetti2020] Section 4 (locator not verified) | Against the dummy adversary. | — |
| `Protocols.UC.EmulatesBlackBoxWithin` | standard | [Canetti2020] Section 4 (locator not verified) | One black-box simulator. | — |

## Generic vocabulary

These notions state the security of whatever the caller supplies: two games or ensembles, an adversary predicate, a resource budget or a bound. They are not assumptions by themselves, and a nonvacuity test belongs to an instance, not to the notion. Under a cited headline, review checks that the instance a theorem supplies is the source's assumption ([AGENTS.md, Security theorems](../../AGENTS.md#security-theorems)): `ComputationallyIndistinguishable` of a scheme's keys and an ideal key law, for example, is a premise about the scheme's own algorithms.

| Assumption | Status | Source definition | Deviations or relation | Nonvacuity |
|---|---|---|---|---|
| `Game.Indistinguishable` | vocabulary | — | Negligible advantage between two caller-supplied game families for every adversary that a caller's predicate admits. | — |
| `Game.IndistinguishableWithError` | vocabulary | — | A common concrete bound `ε n` on that advantage for every admitted adversary. | — |
| `Game.IndistinguishableWithin` | vocabulary | — | Concrete `(Within, ε)`-indistinguishability against a resource predicate that the caller supplies. | — |
| `Game.SuccWithin` | vocabulary | — | Concrete one-sided security against a resource predicate that the caller supplies. | — |
| `ComputationallyIndistinguishable` | vocabulary | — | Two caller-supplied word ensembles against uniform strict PPT distinguishers; neither ensemble need be efficiently samplable or polynomially bounded in length. | — |
| `IndistinguishableWithAdvice` | vocabulary | — | Two caller-supplied ensembles against uniform strict PPT tests that also read one fixed advice family; with empty advice it is `ComputationallyIndistinguishable`. | — |
| `NonuniformlyIndistinguishable` | vocabulary | — | `IndistinguishableWithAdvice` for every polynomially bounded advice family: non-uniform indistinguishability of two caller-supplied ensembles, with the advice length charged to the test's clock. | — |
| `NativeQuantum.ComputationallyIndistinguishable` | vocabulary | — | Two caller-supplied ensembles against native uniform quantum tests without advice or a useful oracle. | — |
| `NativeQuantum.IndistinguishableWithin` | vocabulary | — | Concrete form of `NativeQuantum.ComputationallyIndistinguishable`, with separate circuit resource budgets. | — |
