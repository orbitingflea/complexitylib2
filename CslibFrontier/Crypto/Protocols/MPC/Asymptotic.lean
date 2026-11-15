/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.DPi
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.PPT
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Crypto.Protocols.MPC.Basic

/-!
# Asymptotic computational semi-honest security of protocol families

`semiHonestAdvantage` measures one run of one protocol on one input tuple. This module gives the
asymptotic notion: a `ProtocolFamily` has a protocol for each security parameter `n` and public
parameters `d`, and `ProtocolFamily.SemiHonestSecure P setup I E` says that, with `d` drawn from
the setup law `setup n`, some PPT simulator family for the coalition `I` makes the real and ideal
runs indistinguishable for every PPT environment.

An environment (`Environment`) has two stages. Given `n` and `d`, it chooses all parties' inputs
and keeps a state (`InputChoice`); after the run, it sees the views of the parties in `I` and the
outputs of all parties, and returns a bit. In `ProtocolFamily.realGame` the views come from a run
of the protocol; in `ProtocolFamily.idealGame` the outputs come from the functionality and a
simulator computes the views from the inputs and outputs of the parties in `I`.

Efficiency is stated on encodings. A `ProtocolFamily.Encoding` writes the public parameters as a
word and, for each party, its inputs, outputs and views as values of a fixed type with a fixed
encoding (`PartyEncoding`), so that a protocol can represent group elements or other
parameter-dependent values as records of words. An environment is PPT (`Environment.IsPPT`) when
one uniform strict PPT machine computes each stage: the first reads `(1ⁿ, d)` and writes the
inputs and the state, the second reads `encGuessInput`. A simulator family is PPT
(`SimulatorFamily.IsPPT`) when one uniform strict PPT machine reads `encSimInput`, which holds
`1ⁿ`, `d` and the coalition's inputs and outputs, and writes the simulated views.

`ProtocolFamily.SemiHonestSecure.of_perfect` is the first property: a protocol family that is
perfectly private at every `n` and `d` (the ideal and real joint distributions are equal) with a
PPT simulator family is secure. `ProtocolFamily.realGame_eq_idealGame` is its game form, and
`ProtocolFamily.advantage_idealGame_le` bounds the effect of replacing one simulator family by a
statistically close one, as a protocol does when its exact simulator samples values that a
bounded-time machine can only approximate.

## Comparison with the sources

[Lindell2017], Section 4.2, Definition 4.1 (p. 7) defines security of a two-party protocol against
static semi-honest adversaries: there are PPT simulators `S₁, S₂` such that `S_i(1ⁿ, x_i, f_i(x))`
paired with the functionality's output `f(x)` is computationally indistinguishable from party
`i`'s view paired with both parties' outputs. [Goldreich2004], Definition 7.5.1 (general case,
Eq. 7.40) is the `m`-party form, with a coalition `I` in place of one party.
`SemiHonestSecure P setup I E` is the corresponding requirement for the coalition `I`; for two
parties, Definition 4.1 corresponds to `∀ i, SemiHonestSecure P setup {i} E`, with these
differences:

* **Uniform environments that choose the inputs.** In the sources the ensembles are indexed by the
  inputs and the security parameter, and indistinguishability is against non-uniform
  polynomial-time distinguishers with one negligible function for all inputs ([Lindell2017],
  Section 2, p. 3; Lindell's p. 9 notes that auxiliary input enters through this
  non-uniformity). Here the environment is a uniform strict PPT machine that chooses the inputs,
  after seeing `d`, and the negligible function may depend on the environment. A non-uniform
  distinguisher can hard-wire the worst inputs for each `n`; a uniform environment must find
  them, so the notion here is the uniform variant and is weaker.
* **Public setup.** The public parameters are drawn from an arbitrary setup law and given to the
  environment and the simulator. The sources have no setup; a deterministic setup law corresponds
  to them. The setup law need not be efficiently samplable.
* **One coalition at a time.** `SemiHonestSecure P setup I E` is for one static coalition `I`,
  with its own simulator family. Definition 7.5.1 has one simulator that receives `I`; for a fixed
  number of parties the two forms are equivalent.
* **Typed inputs and the stand-alone model.** Inputs, outputs and views are typed values written
  as words by `E`, not strings of equal length; review checks that a protocol's encoding is the
  natural one. The run is stand-alone: one execution, without other protocols running beside it.
* **Strict PPT in the input length.** Environments and simulators are uniform strict PPT machines
  (`IsPPTOn`): every run halts within a polynomial in the length of the machine's whole encoded
  input, which includes `1ⁿ` and, for a simulator, the coalition's inputs and outputs, as in
  [Goldreich2004]. [Lindell2017] (p. 3) bounds a party's running time in the security parameter
  alone. The inputs here are chosen by a PPT environment that reads `1ⁿ` and the public
  parameters `d`, so their length is polynomial in the length of that whole encoded input,
  `encPair encUnary E.desc`. It is polynomial in `n` only when the words `E.desc d` are, which
  neither `ProtocolFamily` nor `SemiHonestSecure` requires: a setup law may supply a `2 ^ n`-bit
  public word that the environment copies into an input.
* The notion constrains only the simulator and the environment. The efficiency and correctness of
  the honest parties' algorithms, which the sources assume, are separate properties of a
  protocol family.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ProtocolFamily`: protocols indexed by a security parameter and
  public parameters.
* `Cslib.Crypto.Protocols.MPC.InputChoice`, `Cslib.Crypto.Protocols.MPC.Environment`: two-stage
  environments.
* `Cslib.Crypto.Protocols.MPC.SimulatorFamily`: simulator families for a coalition.
* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.realGame`,
  `Cslib.Crypto.Protocols.MPC.ProtocolFamily.idealGame`: the real and ideal games.
* `Cslib.Crypto.Protocols.MPC.PartyEncoding`, `Cslib.Crypto.Protocols.MPC.ProtocolFamily.Encoding`,
  `Cslib.Crypto.Protocols.MPC.GuessInput`, `Cslib.Crypto.Protocols.MPC.encGuessInput`,
  `Cslib.Crypto.Protocols.MPC.SimInput`, `Cslib.Crypto.Protocols.MPC.encSimInput`: what machines
  read and write.
* `Cslib.Crypto.Protocols.MPC.Environment.IsPPT`,
  `Cslib.Crypto.Protocols.MPC.SimulatorFamily.IsPPT`: PPT environments and simulator families.
* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.SemiHonestSecure`: asymptotic computational
  semi-honest security against a static coalition.

## Main results

* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.SemiHonestSecure.of_perfect`: perfect privacy with a
  PPT simulator family gives security.
* `Cslib.Crypto.Protocols.MPC.ProtocolFamily.advantage_idealGame_le`: statistically close
  simulator families give close ideal games.
* `Cslib.Crypto.Protocols.MPC.PartyEncoding.encCoalition_singleton`: the word of a single party's
  values, as two-party certificates use it.

`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Simulators.lean` proves the notion for DDH oblivious
transfer from the DDH assumption (`Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTSemiHonestSecure`).
The test module `CslibFrontierTests.Crypto.MPCAsymptotic` refutes it for a protocol that leaks a
party's input bit, with a PPT environment, and proves it without assumptions for the protocol that
delivers the bit as the functionality's output, through `SemiHonestSecure.of_perfect`.

## References

* [Y. Lindell, *How To Simulate It – A Tutorial on the Simulation Proof Technique*, ECCC
  TR17-112][Lindell2017], Section 2 (p. 3) and Section 4.2 (Definition 4.1, p. 7; auxiliary
  information, p. 9).
* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004],
  Section 7.5.1.2 (Definition 7.5.1).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Cslib.Probability Turing.MultiTapeTM
open scoped NNReal

variable {m : ℕ}

/-! ### Protocol families, environments and simulators -/

/-- A family of `m`-party protocols: for each security parameter `n` and public parameters `d`, a
protocol `protocol n d` in the oracle world `world n d` for the functionality `functionality n d`.
The law of the public parameters is a separate argument of the games, as for `F.DDH setup`. -/
structure ProtocolFamily (m : ℕ) where
  /-- The type of public parameters. -/
  Desc : Type
  /-- The oracle specification of the hybrid model; `noOracleSpec` in the plain model. -/
  spec : ℕ → Desc → MultiOracleSpec
  /-- The schedule of rounds. -/
  sc : (n : ℕ) → (d : Desc) → Schedule m (spec n d)
  /-- The parties' input types. -/
  In : ℕ → Desc → Fin m → Type
  /-- The parties' coin types. -/
  Coins : ℕ → Desc → Fin m → Type
  /-- The parties' output types. -/
  Out : ℕ → Desc → Fin m → Type
  /-- The protocol. -/
  protocol : (n : ℕ) → (d : Desc) →
    Protocol m (spec n d) (sc n d) (In n d) (Coins n d) (Out n d)
  /-- The oracle world in which the protocol runs; `noOracleWorld` in the plain model. -/
  world : (n : ℕ) → (d : Desc) → MultiOracleWorld (spec n d)
  /-- The functionality that the protocol computes. -/
  functionality : (n : ℕ) → (d : Desc) → Functionality m (In n d) (Out n d)

/-- The inputs that an environment chooses for one run of `P` at `n` and `d`, and the state it
keeps for its guess. -/
structure InputChoice (P : ProtocolFamily m) (n : ℕ) (d : P.Desc) where
  /-- The inputs of all parties. -/
  inputs : (i : Fin m) → P.In n d i
  /-- The state passed to the guessing stage. -/
  state : List Bool

/-- A two-stage environment against `P` when the parties in `I` are corrupted. Given the security
parameter `n` and public parameters `d`, `choose` picks all parties' inputs and a state; `guess`
sees the state, the views of the parties in `I` and the outputs of all parties, and returns a
bit. -/
structure Environment (P : ProtocolFamily m) (I : Finset (Fin m)) where
  /-- Choose the inputs of all parties and a state. -/
  choose : (n : ℕ) → (d : P.Desc) → ProbComp (InputChoice P n d)
  /-- Guess from the state, the views of the parties in `I` and the outputs of all parties. -/
  guess : (n : ℕ) → (d : P.Desc) → List Bool →
    ((i : I) → PartyView (P.In n d) (P.Coins n d) (P.sc n d) i) × ((i : Fin m) → P.Out n d i) →
      ProbComp Bool

/-- A simulator family for the coalition `I` of `P`: for each `n` and `d`, a simulator that
produces the views of the parties in `I` from their inputs and outputs. Nothing here asks it to be
efficient; `SimulatorFamily.IsPPT` does. -/
abbrev SimulatorFamily (P : ProtocolFamily m) (I : Finset (Fin m)) : Type :=
  (n : ℕ) → (d : P.Desc) → CoalitionSimulator (P.sc n d) (P.In n d) (P.Coins n d) (P.Out n d) I

namespace ProtocolFamily

variable (P : ProtocolFamily m) (setup : ℕ → PMF P.Desc) (I : Finset (Fin m))

/-- The real game: draw public parameters `d` from the setup law, let `Z` choose the inputs, run
the protocol, and give `Z` the views of the parties in `I` and all outputs. -/
@[expose] noncomputable def realGame (Z : Environment P I) (n : ℕ) : Game := do
  let d ← setup n
  let c ← ProbComp.eval (Z.choose n d)
  let r ← (P.protocol n d).realJoint (P.world n d) I c.inputs
  ProbComp.eval (Z.guess n d c.state r)

/-- The ideal game: draw public parameters `d` from the setup law, let `Z` choose the inputs,
compute the outputs with the functionality, let `S n d` produce the views of the parties in `I`
from their inputs and outputs, and give `Z` these views and all outputs. -/
@[expose] noncomputable def idealGame (S : SimulatorFamily P I) (Z : Environment P I) (n : ℕ) :
    Game := do
  let d ← setup n
  let c ← ProbComp.eval (Z.choose n d)
  let r ← ProbComp.eval (idealJoint (P.functionality n d) I (S n d) c.inputs)
  ProbComp.eval (Z.guess n d c.state r)

end ProtocolFamily

/-! ### Encodings and efficiency -/

/-- How machines read and write the values `X n d i` of each party `i`: as values of a fixed type
`Rep i` with the fixed encoding `enc i`, through an injective map `rep n d i` at each security
parameter and public parameters. A fixed type lets certificates use the polynomial-time calculus
on representations, such as records of words for group elements. -/
structure PartyEncoding (Desc : Type) (m : ℕ) (X : ℕ → Desc → Fin m → Type) where
  /-- The representation type of party `i`'s values. -/
  Rep : Fin m → Type
  /-- The encoding of party `i`'s representations. -/
  enc : (i : Fin m) → Rep i ↪ List Bool
  /-- The representation of party `i`'s values at `n` and `d`. -/
  rep : (n : ℕ) → (d : Desc) → (i : Fin m) → X n d i ↪ Rep i

namespace PartyEncoding

variable {Desc : Type} {X : ℕ → Desc → Fin m → Type} (e : PartyEncoding Desc m X)

/-- The word of the values of all parties at `n` and `d`: the table (`encDPi`) of their
representations. -/
@[expose] noncomputable def encAll (n : ℕ) (d : Desc) : ((i : Fin m) → X n d i) ↪ List Bool where
  toFun x := encDPi e.enc fun i => e.rep n d i (x i)
  inj' _ _ h := funext fun i => (e.rep n d i).injective (congrFun ((encDPi e.enc).injective h) i)

/-- The word of the values of the parties in `I` at `n` and `d`: the table (`encDPi`) of their
representations. -/
@[expose] noncomputable def encCoalition (n : ℕ) (d : Desc) (I : Finset (Fin m)) :
    ((i : I) → X n d i) ↪ List Bool where
  toFun x := encDPi (fun i : I => e.enc i) fun i => e.rep n d i (x i)
  inj' _ _ h := funext fun i =>
    (e.rep n d i).injective (congrFun ((encDPi fun i : I => e.enc i).injective h) i)

/-- The word of the values of a single party `i`: the one-entry table of its representation. -/
theorem encCoalition_singleton (n : ℕ) (d : Desc) (i : Fin m)
    (x : (j : ({i} : Finset (Fin m))) → X n d j) :
    e.encCoalition n d {i} x = encPi encBits fun _ : ({i} : Finset (Fin m)) =>
      e.enc i (e.rep n d i (x ⟨i, Finset.mem_singleton_self i⟩)) := by
  simp only [encCoalition, Function.Embedding.coeFn_mk, encDPi_apply]
  congr 1
  funext ⟨j, hj⟩
  obtain rfl := Finset.mem_singleton.mp hj
  rfl

end PartyEncoding

/-- How machines read and write the public parameters, inputs, outputs and views of a protocol
family. The encoding is part of what `ProtocolFamily.SemiHonestSecure` claims: it fixes the input
lengths that bound the running time of environments and simulators. -/
structure ProtocolFamily.Encoding (P : ProtocolFamily m) where
  /-- The encoding of the public parameters. -/
  desc : P.Desc ↪ List Bool
  /-- The representation of the parties' inputs. -/
  input : PartyEncoding P.Desc m P.In
  /-- The representation of the parties' outputs. -/
  output : PartyEncoding P.Desc m P.Out
  /-- The representation of the parties' views. -/
  view : PartyEncoding P.Desc m fun n d i => PartyView (P.In n d) (P.Coins n d) (P.sc n d) i

/-- The input of an environment's guessing stage against `P` with the parties in `I` corrupted, as
a record: the security parameter, the public parameters, the saved state, the views of the parties
in `I` and the outputs of all parties. -/
structure GuessInput (P : ProtocolFamily m) (I : Finset (Fin m)) where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public parameters. -/
  desc : P.Desc
  /-- The state saved by the choosing stage. -/
  state : List Bool
  /-- The views of the parties in `I`. -/
  views : (i : I) → PartyView (P.In secParam desc) (P.Coins secParam desc) (P.sc secParam desc) i
  /-- The outputs of all parties. -/
  outputs : (i : Fin m) → P.Out secParam desc i

/-- The input of a simulator for the coalition `I` of `P`, as a record: the security parameter,
the public parameters, and the inputs and outputs of the parties in `I`. -/
structure SimInput (P : ProtocolFamily m) (I : Finset (Fin m)) where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- The public parameters. -/
  desc : P.Desc
  /-- The inputs of the parties in `I`. -/
  inputs : (i : I) → P.In secParam desc i
  /-- The outputs of the parties in `I`. -/
  outputs : (i : I) → P.Out secParam desc i

variable {P : ProtocolFamily m} {I : Finset (Fin m)}

noncomputable section

/-- The encoding of a guessing-stage input: the unary security parameter, the public parameters
`E.desc d`, the state, the word of the views of the parties in `I` (`PartyEncoding.encCoalition`)
and the word of all outputs (`PartyEncoding.encAll`), each framed except the last. -/
enc_structure encGuessInput (E : P.Encoding) : GuessInput P I where
  secParam : encUnary, desc : E.desc, state : encBits,
  views : (E.view.encCoalition secParam desc I)
    using (E.view.encCoalition secParam desc I).injective,
  outputs : (E.output.encAll secParam desc) using (E.output.encAll secParam desc).injective

/-- The encoding of a simulator's input: the unary security parameter, the public parameters
`E.desc d`, and the words of the inputs and of the outputs of the parties in `I`
(`PartyEncoding.encCoalition`), each framed except the last. -/
enc_structure encSimInput (E : P.Encoding) : SimInput P I where
  secParam : encUnary, desc : E.desc,
  inputs : (E.input.encCoalition secParam desc I)
    using (E.input.encCoalition secParam desc I).injective,
  outputs : (E.output.encCoalition secParam desc I)
    using (E.output.encCoalition secParam desc I).injective

end

/-- An environment is PPT for the encoding `E` when its choosing stage is computed by a uniform
strict PPT machine that reads the unary security parameter and the public parameters and writes
the table of the representations of the chosen inputs and the state, and its guessing stage by
one that reads `encGuessInput E` and writes the output bit. -/
structure Environment.IsPPT (E : P.Encoding) (Z : Environment P I) : Prop where
  /-- The choosing stage is uniform strict PPT. -/
  choose : IsPPTOn (encPair encUnary E.desc) (encPair (encDPi E.input.enc) encBits)
    fun (n, d) =>
      (fun c => ((fun i => E.input.rep n d i (c.inputs i)), c.state)) <$> Z.choose n d
  /-- The guessing stage is uniform strict PPT. -/
  guess : IsPPTOn (encGuessInput E) encBool
    fun y => Z.guess y.secParam y.desc y.state (y.views, y.outputs)

/-- A simulator family is PPT for the encoding `E` when one uniform strict PPT machine reads
`encSimInput E` and writes the table of the representations of the simulated views. -/
@[expose] def SimulatorFamily.IsPPT (E : P.Encoding) (S : SimulatorFamily P I) : Prop :=
  IsPPTOn (encSimInput E) (encDPi fun i : I => E.view.enc i) fun x =>
    (fun v i => E.view.rep x.secParam x.desc i (v i)) <$>
      S x.secParam x.desc x.inputs x.outputs

namespace ProtocolFamily

/-- **Asymptotic semi-honest security** of the protocol family `P` with public parameters drawn
from `setup`, against the static coalition `I`, for the encoding `E` ([Lindell2017],
Definition 4.1, for each corrupted party; [Goldreich2004], Definition 7.5.1, for a coalition):
some simulator family `S`, PPT for `E`, makes the real game and the ideal game with `S`
indistinguishable for every PPT environment. The environments are uniform and choose the inputs,
and the public parameters come from a setup law; the module documentation lists these and the
other differences from the sources. -/
@[expose] def SemiHonestSecure (P : ProtocolFamily m) (setup : ℕ → PMF P.Desc)
    (I : Finset (Fin m)) (E : P.Encoding) : Prop :=
  ∃ S : SimulatorFamily P I, S.IsPPT E ∧
    Game.Indistinguishable (P.realGame setup I) (P.idealGame setup I S) (Environment.IsPPT E)

/-- Perfect privacy makes the games equal: if at every `n` and `d` the ideal joint distribution
with `S n d` equals the real one, the real game and the ideal game with `S` are equal for every
environment. -/
theorem realGame_eq_idealGame {setup : ℕ → PMF P.Desc} {S : SimulatorFamily P I}
    (h : ∀ n d x, ProbComp.eval (idealJoint (P.functionality n d) I (S n d) x) =
      (P.protocol n d).realJoint (P.world n d) I x)
    (Z : Environment P I) (n : ℕ) : P.realGame setup I Z n = P.idealGame setup I S Z n := by
  simp only [realGame, idealGame, h]

/-- **Replacing a simulator family by a close one.** If at the security parameter `n` the
simulators `S n d` and `S' n d` are within `ε` on every input against every test, the ideal games
with `S` and with `S'` are within `ε` for every environment. -/
theorem advantage_idealGame_le {setup : ℕ → PMF P.Desc} {S S' : SimulatorFamily P I} {ε : ℝ≥0}
    {n : ℕ}
    (h : ∀ d xI yI (k : ((i : I) → PartyView (P.In n d) (P.Coins n d) (P.sc n d) i) → Game),
      Game.advantage ((ProbComp.eval (S n d xI yI)).bind k)
        ((ProbComp.eval (S' n d xI yI)).bind k) ≤ ε)
    (Z : Environment P I) :
    Game.advantage (P.idealGame setup I S Z n) (P.idealGame setup I S' Z n) ≤ ε := by
  simp only [idealGame, eval_idealJoint, PMF.monad_bind_eq_bind, PMF.bind_bind, PMF.bind_map,
    Function.comp_def]
  exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
    Game.advantage_bind_le_nnreal _ _ _ fun _ =>
      Game.advantage_bind_le_nnreal _ _ _ fun _ => h d _ _ _

/-- **Perfect privacy with PPT simulators gives security.** If at every `n` and `d` the ideal joint
distribution with `S n d` equals the real one, and `S` is PPT for `E`, then `P` is semi-honest
secure against `I` for `E`. -/
theorem SemiHonestSecure.of_perfect {setup : ℕ → PMF P.Desc} {E : P.Encoding}
    {S : SimulatorFamily P I} (hS : S.IsPPT E)
    (h : ∀ n d x, ProbComp.eval (idealJoint (P.functionality n d) I (S n d) x) =
      (P.protocol n d).realJoint (P.world n d) I x) :
    P.SemiHonestSecure setup I E :=
  ⟨S, hS, fun Z _ => by
    simp only [realGame_eq_idealGame h, Game.advantage_self]
    exact negligible_zero⟩

end ProtocolFamily

end Cslib.Crypto.Protocols.MPC
