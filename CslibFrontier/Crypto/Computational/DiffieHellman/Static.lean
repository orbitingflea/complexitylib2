/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount

/-!
# Static Diffie–Hellman and chosen-ciphertext key recovery against multiplicative ElGamal

Fix an additive commutative group `G` that is a `ZMod q`-module, as in
`CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean`; the textbook element `v ^ α` is
`α • v` and the identity `1` is `0`.

In the static Diffie–Hellman (SDH) experiment ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688), the challenger draws a uniform secret `α : ZMod q` and answers each query `v : G` with
`α • v` (`sdhOracle`); the adversary wins when it outputs `α` (`sdhExperiment`, `sdhAdvantage`).
With one query at `g`, a discrete-logarithm adversary `A` plays `dlExperiment q g A` inside
`sdhExperiment` (`dlToSDH`, `sdhAdvantage_dlToSDH`).

Multiplicative ElGamal ([BonehShoup2023], Exercise 11.5, p. 459) decrypts a ciphertext
`(v, e) : G × G` under secret key `α : ZMod q` to `e - α • v`. As observed in [BonehShoup2023],
Section 16.1.4 (p. 688), decrypting `(-v, 0)` (the additive form of `(1 / v, 1)`) returns
`0 - α • (-v) = α • v` (`elGamalDecryptOracle_neg_zero`). Consequently, answering each SDH query
`v` by asking the ElGamal decryption oracle `elGamalDecryptOracle` for `(-v, 0)` turns any
static-DH adversary `A` into a key-recovery oracle adversary `sdhToElGamalKeyRecovery A` with the
exact same experiment distribution and success probability
(`elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery`), preserving any query budget `Q`
(`isQueryBounded_sdhToElGamalKeyRecovery`) and submitting only ciphertexts with second component `0`
(`queriesSatisfy_sdhToElGamalKeyRecovery`). Conversely, an ElGamal key-recovery adversary `B` making
at most `Q` decryption queries gives a static-DH adversary `elGamalKeyRecoveryToSDH g B` making at
most `Q + 1` SDH queries (one query at `g` for the public key `α • g`, plus one per decryption
query) with the same advantage (`sdhAdvantage_elGamalKeyRecoveryToSDH`,
`isQueryBounded_elGamalKeyRecoveryToSDH`).

All definitions and reductions here are stated for one fixed group with per-reduction query bounds
(`isQueryBounded_dlToSDH`, `isQueryBounded_sdhToElGamalKeyRecovery`,
`isQueryBounded_elGamalKeyRecoveryToSDH`) and query predicates (`queriesSatisfy_dlToSDH`,
`queriesSatisfy_sdhToElGamalKeyRecovery`), with no PPT efficiency certificate over a group family
(such as `IsOraclePPT` / `IsOraclePPTOn`), no asymptotic SDH assumption, no one-more
Diffie–Hellman reduction, and no Brown–Gallant–Cheon attack ([BonehShoup2023], Exercise 16.3).

## Differences from the book

* Groups are written additively as `ZMod q`-modules: `1` is `0`, `v ^ α` is `α • v`, `1 / v` is
  `-v`, and the decryption query `(1 / v, 1)` is `(-v, 0)`.
* The fixed-group definitions and theorems assume only `[AddCommGroup G]`, `[NeZero q]` and
  `[Module (ZMod q) G]`; neither primality of `q` nor that `g` generates `G` is required.
* [BonehShoup2023], Section 16.1.4 (p. 688) states Attack Game 16.1 and the reduction
  `sdhToElGamalKeyRecovery`. `dlToSDH` and the converse `elGamalKeyRecoveryToSDH` are additions of
  this library. `dlToSDH` shows that the game is no harder than discrete logarithm; the book's
  expectation that it is no easier, which it qualifies on the same page, is not formalized.
* `elGamalKeyRecoveryExperiment` is a stand-alone key-recovery oracle game backed by the algebraic
  decryption oracle `elGamalDecryptOracle` (computing `pure (ct.2 - α • ct.1)`, matching
  `PrimeOrderGroupFamily.elGamalDecrypt`), rather than the `cca2GameOn` indistinguishability game
  used for ElGamal in `CslibFrontier/Crypto/Computational/ElGamal/Malleability.lean`.
* In Attack Game 16.1 the challenger sends no initial group element to the SDH adversary, whereas in
  `elGamalKeyRecoveryExperiment` the adversary receives the public key `α • g`. Thus
  `sdhToElGamalKeyRecovery` ignores the public key and preserves the query bound `Q`, while
  `elGamalKeyRecoveryToSDH` queries `g` once to form `α • g` and has query bound `Q + 1`.

## Main definitions

* `Cslib.Crypto.SDHSpec`, `Cslib.Crypto.SDHAdversary`, `Cslib.Crypto.sdhOracle`,
  `Cslib.Crypto.sdhExperiment`, `Cslib.Crypto.sdhAdvantage`: Attack Game 16.1 in a fixed group.
* `Cslib.Crypto.dlToSDH`: the 1-query discrete-logarithm to static-DH reduction.
* `Cslib.Crypto.ElGamalDecryptionSpec`, `Cslib.Crypto.ElGamalKeyRecoveryAdversary`,
  `Cslib.Crypto.elGamalDecryptOracle`, `Cslib.Crypto.elGamalKeyRecoveryExperiment`,
  `Cslib.Crypto.elGamalKeyRecoveryAdvantage`: the multiplicative ElGamal key-recovery oracle game.
* `Cslib.Crypto.sdhToElGamalKeyRecovery`, `Cslib.Crypto.elGamalKeyRecoveryToSDH`: the reductions
  between static DH and ElGamal key recovery.

## Main results

* `Cslib.Crypto.sdhAdvantage_dlToSDH`, `Cslib.Crypto.isQueryBounded_dlToSDH`,
  `Cslib.Crypto.queriesSatisfy_dlToSDH`: discrete logarithm reduces to 1-query static DH.
* `Cslib.Crypto.elGamalDecryptOracle_neg_zero`: querying `elGamalDecryptOracle` at `(-v, 0)` equals
  `sdhOracle q α v`.
* `Cslib.Crypto.elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.isQueryBounded_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.queriesSatisfy_sdhToElGamalKeyRecovery`: static DH reduces to ElGamal key recovery
  with the same advantage and query budget `Q`.
* `Cslib.Crypto.sdhAdvantage_elGamalKeyRecoveryToSDH`,
  `Cslib.Crypto.isQueryBounded_elGamalKeyRecoveryToSDH`: ElGamal key recovery with budget `Q`
  reduces to static DH with budget `Q + 1`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.5 (p. 459) and Section 16.1.4 (Attack Game 16.1,
  p. 688).
-/

public section

namespace Cslib.Crypto

open Probability
open scoped NNReal ENNReal

section FixedGroup

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)

/-! ### Static Diffie–Hellman (Attack Game 16.1) -/

/-- The oracle interface of the static Diffie–Hellman game ([BonehShoup2023], Section 16.1.4,
Attack Game 16.1, p. 688): each query is a group element `v : G` and is answered by a group
element. -/
abbrev SDHSpec (G : Type) : OracleSpec G := fun _ => G

/-- An adversary for the static Diffie–Hellman game in a group `G` of exponent modulus `q`: a
randomized oracle program over `SDHSpec G` that outputs a guess in `ZMod q`. -/
abbrev SDHAdversary (G : Type) (q : ℕ) : Type :=
  ProbOracleComp (SDHSpec G) (ZMod q)

/-- The static Diffie–Hellman solve oracle ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688, and Section 11.6.3, p. 455): on query `v : G`, return `α • v` (the textbook `v ^ α`). This
is also the oracle of the book's CDH solve query in Section 11.6.3 (the one-more Diffie–Hellman
game is not formalized here). -/
@[expose] def sdhOracle (α : ZMod q) (v : G) : ProbComp G :=
  pure (α • v)

/-- The static Diffie–Hellman experiment ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688): draw a uniform secret `α : ZMod q`, run `A` against `sdhOracle q α`, and accept when the
adversary outputs `α`. -/
@[expose] noncomputable def sdhExperiment (A : SDHAdversary G q) : Experiment := do
  let α ← $ᵗ ZMod q
  let guess ← A.run (sdhOracle q α)
  return guess = α

/-- The static Diffie–Hellman advantage of `A`: its success probability in `sdhExperiment`. -/
@[expose] noncomputable def sdhAdvantage (A : SDHAdversary G q) : ℝ≥0 :=
  Experiment.succProbability (sdhExperiment q A)

/-- Turn a discrete-logarithm adversary `A` into a 1-query static Diffie–Hellman adversary: query
the SDH oracle at `g` to obtain `α • g` and run `A` on the reply. -/
def dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) : SDHAdversary G q := do
  let u ← ProbOracleComp.query (spec := SDHSpec G) g
  ProbOracleComp.sample (A u)

omit [NeZero q] in
/-- Running `dlToSDH g A` against `sdhOracle q α` runs `A (α • g)`. -/
@[simp] theorem run_sdhOracle_dlToSDH (A : G → ProbComp (ZMod q)) (α : ZMod q) :
    (dlToSDH g A).run (sdhOracle q α) = A (α • g) := by
  simp [dlToSDH, sdhOracle]

/-- In `sdhExperiment`, `dlToSDH g A` is the discrete-logarithm experiment `dlExperiment q g A`. -/
@[simp] theorem sdhExperiment_dlToSDH (A : G → ProbComp (ZMod q)) :
    sdhExperiment q (dlToSDH g A) = dlExperiment q g A := by
  simp [sdhExperiment, dlExperiment]

/-- `dlToSDH g A` wins the static Diffie–Hellman game with the exact discrete-logarithm advantage
of `A`. -/
@[simp] theorem sdhAdvantage_dlToSDH (A : G → ProbComp (ZMod q)) :
    sdhAdvantage q (dlToSDH g A) = dlAdvantage q g A := by
  simp [sdhAdvantage, dlAdvantage]

omit [AddCommGroup G] in
/-- `dlToSDH g A` makes at most `1` SDH query on every path. -/
theorem isQueryBounded_dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) :
    (dlToSDH g A).IsQueryBounded 1 := by
  simpa [dlToSDH] using
    (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) g).bind fun u =>
      ProbOracleComp.IsQueryBounded.sample (spec := SDHSpec G) (A u)

omit [AddCommGroup G] in
/-- Every SDH query made by `dlToSDH g A` is `g`. -/
theorem queriesSatisfy_dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) :
    (dlToSDH g A).QueriesSatisfy (· = g) := by
  simpa [dlToSDH, ProbOracleComp.QueriesSatisfy] using
    (ProbOracleComp.QueriesSatisfy.query (spec := SDHSpec G) (p := (· = g)) rfl).bind fun u =>
      ProbOracleComp.QueriesSatisfy.sample (spec := SDHSpec G) (A u)

/-! ### Key-recovery oracle attack on multiplicative ElGamal -/

/-- The decryption oracle interface of multiplicative ElGamal ([BonehShoup2023], Exercise 11.5,
p. 459, and Section 16.1.4, p. 688): a query is a ciphertext pair `(v, e) : G × G` and is answered
by the decrypted group element in `G`. -/
abbrev ElGamalDecryptionSpec (G : Type) : OracleSpec (G × G) := fun _ => G

/-- A key-recovery decryption-oracle adversary against multiplicative ElGamal: given the public key
`u = α • g`, it queries the decryption oracle on ciphertexts in `G × G` and outputs a guess for
the secret key `α : ZMod q`. -/
abbrev ElGamalKeyRecoveryAdversary (G : Type) (q : ℕ) : Type :=
  G → ProbOracleComp (ElGamalDecryptionSpec G) (ZMod q)

/-- The multiplicative ElGamal decryption oracle under secret key `α : ZMod q`
([BonehShoup2023], Exercise 11.5, p. 459): decrypts `(v, e)` to `e - α • v` (matching
`PrimeOrderGroupFamily.elGamalDecrypt`). -/
@[expose] def elGamalDecryptOracle (α : ZMod q) (ct : G × G) : ProbComp G :=
  pure (ct.2 - α • ct.1)

omit [NeZero q] in
/-- **Key observation of [BonehShoup2023], Section 16.1.4 (p. 688)**: querying
`elGamalDecryptOracle` at `(-v, 0)` (the additive form of `(1 / v, 1)`) equals `sdhOracle q α v`. -/
@[simp] theorem elGamalDecryptOracle_neg_zero (α : ZMod q) (v : G) :
    elGamalDecryptOracle q α (-v, (0 : G)) = sdhOracle q α v := by
  simp [elGamalDecryptOracle, sdhOracle]

/-- The key-recovery decryption-oracle experiment for multiplicative ElGamal ([BonehShoup2023],
Section 16.1.4, p. 688): draw a uniform secret key `α : ZMod q`, pass the public key `α • g` to `B`
with access to `elGamalDecryptOracle q α`, and accept when `B` outputs `α`. -/
@[expose] noncomputable def elGamalKeyRecoveryExperiment
    (B : ElGamalKeyRecoveryAdversary G q) : Experiment := do
  let α ← $ᵗ ZMod q
  let guess ← (B (α • g)).run (elGamalDecryptOracle q α)
  return guess = α

/-- The key-recovery advantage of `B` against multiplicative ElGamal: its success probability in
`elGamalKeyRecoveryExperiment`. -/
@[expose] noncomputable def elGamalKeyRecoveryAdvantage
    (B : ElGamalKeyRecoveryAdversary G q) : ℝ≥0 :=
  Experiment.succProbability (elGamalKeyRecoveryExperiment q g B)

/-- **The static-DH to ElGamal key-recovery reduction** ([BonehShoup2023], Section 16.1.4, p. 688):
given a static-DH adversary `A`, build the key-recovery adversary `B` that runs `A` and answers each
SDH query `v : G` by querying the ElGamal decryption oracle on `(-v, 0)` (the additive form of
`(1 / v, 1)`). -/
def sdhToElGamalKeyRecovery {q : ℕ} (A : SDHAdversary G q) :
    ElGamalKeyRecoveryAdversary G q :=
  fun _ => ProbOracleComp.simulate (fun v => ProbOracleComp.query (-v, 0)) A

omit [NeZero q] in
/-- Running `sdhToElGamalKeyRecovery A` against the ElGamal decryption oracle runs `A` against the
SDH oracle. -/
@[simp] theorem run_elGamalDecryptOracle_sdhToElGamalKeyRecovery (α : ZMod q)
    (A : SDHAdversary G q) (u : G) :
    (sdhToElGamalKeyRecovery A u).run (elGamalDecryptOracle q α) = A.run (sdhOracle q α) := by
  simp only [sdhToElGamalKeyRecovery, ProbOracleComp.run_simulate, ProbOracleComp.run_query,
    elGamalDecryptOracle_neg_zero]

/-- **The key-recovery experiment of `sdhToElGamalKeyRecovery A` is `sdhExperiment q A`**
([BonehShoup2023], Section 16.1.4, p. 688). -/
@[simp] theorem elGamalKeyRecoveryExperiment_sdhToElGamalKeyRecovery (A : SDHAdversary G q) :
    elGamalKeyRecoveryExperiment q g (sdhToElGamalKeyRecovery A) = sdhExperiment q A := by
  simp [elGamalKeyRecoveryExperiment, sdhExperiment]

/-- **`sdhToElGamalKeyRecovery A` recovers the ElGamal secret key with the exact SDH advantage of
`A`** ([BonehShoup2023], Section 16.1.4, p. 688). -/
@[simp] theorem elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery (A : SDHAdversary G q) :
    elGamalKeyRecoveryAdvantage q g (sdhToElGamalKeyRecovery A) = sdhAdvantage q A := by
  simp [elGamalKeyRecoveryAdvantage, sdhAdvantage]

/-- **Query-bound certificate for `sdhToElGamalKeyRecovery`**: if `A` makes at most `Q` SDH
queries, then `sdhToElGamalKeyRecovery A` makes at most `Q` decryption queries. -/
theorem isQueryBounded_sdhToElGamalKeyRecovery {q : ℕ} {A : SDHAdversary G q} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) (u : G) :
    (sdhToElGamalKeyRecovery A u).IsQueryBounded Q :=
  hQ.simulate fun v => ProbOracleComp.IsQueryBounded.query (spec := ElGamalDecryptionSpec G) (-v, 0)

/-- Every decryption query submitted by `sdhToElGamalKeyRecovery A` has second component `0`
(the textbook `(1 / v, 1)`). -/
theorem queriesSatisfy_sdhToElGamalKeyRecovery {q : ℕ} (A : SDHAdversary G q) (u : G) :
    (sdhToElGamalKeyRecovery A u).QueriesSatisfy fun ct => ct.2 = 0 :=
  ProbOracleComp.queriesSatisfy_simulate (p' := fun ct : G × G => ct.2 = 0)
    (fun v => ProbOracleComp.QueriesSatisfy.query (spec := ElGamalDecryptionSpec G)
      (q := (-v, 0)) rfl)
    A

/-- The converse reduction: turn an ElGamal key-recovery adversary `B` into a static-DH adversary
by querying `g` to obtain the public key `α • g` and answering each decryption query `(v, e)` with
`e - α • v` via one SDH query at `v`. -/
def elGamalKeyRecoveryToSDH {q : ℕ} (g : G) (B : ElGamalKeyRecoveryAdversary G q) :
    SDHAdversary G q := do
  let u ← ProbOracleComp.query (spec := SDHSpec G) g
  ProbOracleComp.simulate
    (fun ct : G × G => do
      let w ← ProbOracleComp.query (spec := SDHSpec G) ct.1
      return ct.2 - w)
    (B u)

omit [NeZero q] in
/-- Running `elGamalKeyRecoveryToSDH g B` against `sdhOracle q α` runs `B (α • g)` against
`elGamalDecryptOracle q α`. -/
@[simp] theorem run_sdhOracle_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q)
    (α : ZMod q) :
    (elGamalKeyRecoveryToSDH g B).run (sdhOracle q α) =
      (B (α • g)).run (elGamalDecryptOracle q α) := by
  simp only [elGamalKeyRecoveryToSDH, ProbOracleComp.run_bind, ProbOracleComp.run_query,
    ProbOracleComp.run_simulate, ProbOracleComp.run_pure, sdhOracle, pure_bind]
  rfl

/-- In `sdhExperiment`, `elGamalKeyRecoveryToSDH g B` is `elGamalKeyRecoveryExperiment q g B`. -/
@[simp] theorem sdhExperiment_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q) :
    sdhExperiment q (elGamalKeyRecoveryToSDH g B) = elGamalKeyRecoveryExperiment q g B := by
  simp [sdhExperiment, elGamalKeyRecoveryExperiment]

/-- `elGamalKeyRecoveryToSDH g B` wins the static-DH game with the exact key-recovery advantage of
`B`. -/
@[simp] theorem sdhAdvantage_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q) :
    sdhAdvantage q (elGamalKeyRecoveryToSDH g B) = elGamalKeyRecoveryAdvantage q g B := by
  simp [sdhAdvantage, elGamalKeyRecoveryAdvantage]

/-- **Query-bound certificate for `elGamalKeyRecoveryToSDH`**: if `B` makes at most `Q` decryption
queries on every public key, then `elGamalKeyRecoveryToSDH g B` makes at most `Q + 1` SDH
queries. -/
theorem isQueryBounded_elGamalKeyRecoveryToSDH {q : ℕ} (g : G)
    {B : ElGamalKeyRecoveryAdversary G q} {Q : ℕ} (hQ : ∀ u, (B u).IsQueryBounded Q) :
    (elGamalKeyRecoveryToSDH g B).IsQueryBounded (Q + 1) := by
  rw [Nat.add_comm]
  refine (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) g).bind fun u => ?_
  refine (hQ u).simulate fun ct => ?_
  simpa using (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) ct.1).bind fun w =>
    OracleComp.IsCostBounded.pure (ct.2 - w) 0

end FixedGroup

end Cslib.Crypto
