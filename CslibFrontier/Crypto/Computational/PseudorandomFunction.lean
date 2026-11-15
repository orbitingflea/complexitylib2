/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
public import CslibFrontier.Computability.Probabilistic.Oracle.Parameter
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Languages.Probabilistic.BitString
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.RandomOracle
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic

/-!
# Uniform computational pseudorandom functions

A keyed family has `n`-bit keys, and its valid queries and answers have `inLen n` and `outLen n`
bits. An adversary receives the unary security parameter, independent private randomness and
adaptive access to one word channel. The real game samples one key; the ideal game samples one
whole function and reuses it across calls. Both games invoke the adversary with empty auxiliary
input and reject malformed queries with the empty word. The table is a semantic specification;
`prfIdealGame_eq_lazy` samples it lazily, and `RandomOracle` certifies a lazy realization of the
length-preserving game for oracle-PPT adversaries.

The keyed evaluator has a uniform deterministic TM certificate on the encoded key/query pair.
Admissible adversaries satisfy `IsOraclePPT`, charging ordinary computation and request writing,
with one machine and polynomial for all parameters and auxiliary inputs.

`PseudorandomFunction` is the length-preserving case `inLen = outLen = id`, in which keys, valid
queries and answers all have `n` bits.

## Main definitions

* `Cslib.Crypto.OracleDistinguisher`: a parameterized randomized adaptive oracle test.
* `Cslib.Crypto.prfRealGame`, `.prfIdealGame`: the keyed and random-function experiments.
* `Cslib.Crypto.PseudorandomFunctionOver`: efficient evaluation, lengths and adaptive security.
* `Cslib.Crypto.PseudorandomFunction`: its length-preserving case.

## Main results

* `Cslib.Crypto.interpret_randomFunctionQuery`: correctness of the finite-domain adapter.
* `Cslib.Crypto.prfIdealGame_eq_lazy`: an exact lazy implementation of the ideal experiment.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
* [O. Goldreich, S. Goldwasser, S. Micali, *How to Construct Random Functions*][GGM1986].

Adapted from Crypto/Computational/PseudorandomFunction.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the shared typed interpreter and word channel.
-/

@[expose] public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- An adaptive test with a unary parameter, an auxiliary word and one external word channel. -/
abbrev OracleDistinguisher := ℕ → List Bool → WordOracleComp Unit Bool

/-- A keyed oracle rejects queries outside the declared domain. -/
def prfOracle (family : List Bool → List Bool → List Bool) (n : ℕ) (key query : List Bool) :
    List Bool := if query.length = n then family key query else []

/-- Read a fixed random table on `n`-bit inputs, rejecting malformed words before interpreting
their bits. -/
def randomFunctionOracle (n : ℕ) {w : ℕ} (table : BitString n → BitString w)
    (query : List Bool) : List Bool :=
  if query.length = n then List.ofFn (table (BitString.ofList n query)) else []

/-- Adapt a valid word to the finite domain. Malformed words make no external call. -/
def randomFunctionQuery (n : ℕ) {w : ℕ} (query : List Bool) :
    ProbOracleComp (fun _ : BitString n => BitString w) (List Bool) :=
  if query.length = n then List.ofFn <$> ProbOracleComp.query (BitString.ofList n query)
  else pure []

/-- The finite query adapter preserves the word-valued table interface in every lawful monad. -/
theorem interpret_randomFunctionQuery {m : Type → Type*} [Monad m] [LawfulMonad m]
    (random : (n : ℕ) → m (Fin (n + 1))) (n : ℕ) {w : ℕ} (table : BitString n → BitString w)
    (query : List Bool) :
    OracleComp.interpret (OracleComp.sumHandler random (fun bits => pure (table bits)))
      (randomFunctionQuery n query) = pure (randomFunctionOracle n table query) := by
  by_cases h : query.length = n <;> simp [randomFunctionQuery, randomFunctionOracle, h]

open Classical in
/-- A semantic random-function cache from `n`-bit to `w`-bit strings, retaining only the
finite-domain answers already used. -/
noncomputable def lazyRandomFunctionOracle (n w : ℕ) (query : List Bool) :
    StateT (RandomOracle.Cache (fun _ : BitString n => BitString w)) PMF (List Bool) :=
  OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
      (RandomOracle.answer (fun _ => PMF.uniformOfFintype (BitString w))))
        (randomFunctionQuery n query)

/-- The real experiment of a keyed family with `inLen n`-bit inputs: sample one `n`-bit key and
answer every query of `inLen n` bits with the family under that key, and any other query with the
empty word. -/
noncomputable def prfRealGame (inLen : ℕ → ℕ) (family : List Bool → List Bool → List Bool)
    (adversary : OracleDistinguisher) (n : ℕ) : ProbComp Bool := do
  let key ← BitString.sampleList n
  (adversary n []).run fun request => pure (prfOracle family (inLen n) key request.2)

/-- The ideal experiment with `inLen n`-bit inputs and `outLen n`-bit outputs: sample one uniform
function between them, independently of the adversary's private samples, and answer every query
of `inLen n` bits with its value, and any other query with the empty word. -/
noncomputable def prfIdealGame (inLen outLen : ℕ → ℕ) (adversary : OracleDistinguisher)
    (n : ℕ) : ProbComp Bool := do
  let table ← ProbComp.uniform (BitString (inLen n) → BitString (outLen n))
  (adversary n []).run fun request => pure (randomFunctionOracle (inLen n) table request.2)

/-- The ideal game admits consistent lazy answers to adaptive queries, with private randomness
independent of the table and the same rejection convention for malformed inputs. -/
theorem prfIdealGame_eq_lazy (inLen outLen : ℕ → ℕ) (adversary : OracleDistinguisher) (n : ℕ) :
    ProbComp.eval (prfIdealGame inLen outLen adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun request => lazyRandomFunctionOracle (inLen n) (outLen n) request.2))
            (adversary n [])).run (fun _ => none)).map Prod.fst := by
  classical
  let adapted := OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k))
      (fun request : Unit × List Bool =>
        (randomFunctionQuery (inLen n) request.2 :
          ProbOracleComp (fun _ : BitString (inLen n) => BitString (outLen n)) (List Bool))))
      (adversary n [])
  have h := RandomOracle.uniform_interpret_prob_eq_lazy adapted
  have heager (table : BitString (inLen n) → BitString (outLen n)) (query : List Bool) :
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun bits => PMF.pure (table bits)))
          (randomFunctionQuery (inLen n) query) =
        PMF.pure (randomFunctionOracle (inLen n) table query) :=
    interpret_randomFunctionQuery ProbComp.unifOracle (inLen n) table query
  simpa only [ProbOracleComp.runWith, OracleComp.runWith, adapted, prfIdealGame,
    ProbComp.eval_bind, ProbComp.eval_uniform, ProbOracleComp.eval_run, ProbComp.eval_pure,
    OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
    ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query, heager,
    lazyRandomFunctionOracle, PMF.monad_bind_eq_bind] using h

/-- A keyed family with `n`-bit keys, `inLen n`-bit inputs and `outLen n`-bit outputs, evaluated in
plain polynomial time and secure against every uniform adaptive oracle test: [BonehShoup2023],
Attack Game 4.2 and Definition 4.2, pp. 132–133, for a PRF defined over `(K, X, Y)`, read
asymptotically with `K`, `X` and `Y` the words of `n`, `inLen n` and `outLen n` bits. A query of
another length is answered by the empty word in both games, and deterministic polynomial-time
evaluation is part of the notion. `PseudorandomFunction` is the case `inLen = outLen = id`. -/
structure PseudorandomFunctionOver (inLen outLen : ℕ → ℕ)
    (family : List Bool → List Bool → List Bool) : Prop where
  /-- One deterministic machine evaluates the family from the encoded key and query. -/
  polyTime : ComputableInPolyTime (fun pair => family pair.1 pair.2)
    (encPair encBits encBits) encBits
  /-- Valid queries receive answers of the declared width. -/
  length_eq : ∀ key query, query.length = inLen key.length →
    (family key query).length = outLen key.length
  /-- The real and ideal experiments use the common game-security calculus. -/
  secure : Game.Indistinguishable
    (fun adversary n => ProbComp.eval (prfRealGame inLen family adversary n))
    (fun adversary n => ProbComp.eval (prfIdealGame inLen outLen adversary n))
    (IsOraclePPT encBool)

/-- A length-preserving pseudorandom function: `PseudorandomFunctionOver id id`, whose keys, valid
queries and answers all have `n` bits ([BonehShoup2023], Attack Game 4.2 and Definition 4.2,
pp. 132–133, with `K`, `X` and `Y` all the words of `n` bits). Its fields are those of
`PseudorandomFunctionOver`. -/
abbrev PseudorandomFunction (family : List Bool → List Bool → List Bool) : Prop :=
  PseudorandomFunctionOver id id family

end Cslib.Crypto
