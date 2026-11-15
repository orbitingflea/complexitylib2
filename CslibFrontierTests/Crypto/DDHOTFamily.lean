/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Tactic.Negligible

/-! # DDH oblivious transfer as a protocol family: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family` and of the asymptotic notion in
`CslibFrontier.Crypto.Protocols.MPC.Asymptotic`, under module encapsulation:
* the encoded words of a guessing-stage input, and the words of a receiver's view under
  `ddhOTEncoding`;
* a receiver-corrupting environment that satisfies `Environment.IsPPT`, so the class of admitted
  environments is not empty;
* the concrete bound for a corrupted receiver, and its asymptotic consequence under DDH through
  the reduction's certificate. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTFamily

-- The encoded words of a guessing-stage input: the unary security parameter, the group
-- parameters, the state, the word of the corrupted receiver's view and the word of the outputs,
-- all but the last framed.
example (F : PrimeOrderGroupFamily) (y : GuessInput F.ddhOTFamily {1}) :
    encGuessInput F.ddhOTEncoding y =
      encPair encUnary (encPair F.encDesc (encPair encBits (encPair encBits encBits)))
        (y.secParam, y.desc, y.state,
          F.ddhOTEncoding.view.encCoalition y.secParam y.desc {1} y.views,
          F.ddhOTEncoding.output.encAll y.secParam y.desc y.outputs) :=
  encGuessInput_apply _ y

-- Under `ddhOTEncoding`, a receiver's view is written as its view words.
example (F : PrimeOrderGroupFamily) (n : ℕ) (d : F.Desc)
    (v : PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) 1) :
    F.ddhOTEncoding.view.enc 1 (F.ddhOTEncoding.view.rep n d 1 v) =
      encDDHOTReceiverViewWords (F.ddhOTReceiverViewWords d v) :=
  rfl

/-- The inputs of the environment below: the messages `0` and `g` and the choice bit `false`. -/
noncomputable def constantInputs (F : PrimeOrderGroupFamily) (d : F.Desc) :
    (i : Fin 2) → OTIn (F.Carrier d) i :=
  fun i => Fin.cases (motive := fun i => OTIn (F.Carrier d) i) (0, F.generator d) (fun _ => false) i

/-- A receiver-corrupting environment that sends the messages `0` and `g` with choice bit
`false`, and always guesses `true`. -/
noncomputable def constantEnvironment (F : PrimeOrderGroupFamily) :
    Environment F.ddhOTFamily {1} where
  choose _ d := pure ⟨constantInputs F d, []⟩
  guess _ _ _ _ := pure true

-- The class of PPT environments is not empty.
example (F : PrimeOrderGroupFamily) : (constantEnvironment F).IsPPT F.ddhOTEncoding where
  choose := by
    refine (ComputableInPolyTime.isPPTOn (f := fun p : ℕ × F.Desc =>
      ((fun i => F.ddhOTEncoding.input.rep p.1 p.2 i (constantInputs F p.2 i)), ([] : List Bool)))
      ((ComputableInPolyTime.dpi fun i => ?_).prod (.const []))).congr fun _ => rfl
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => k.elim0) j) i
    · exact (computableInPolyTime_encode_zero (d := fun p : ℕ × F.Desc => p.2) (by fun_prop)).prod
        (computableInPolyTime_encode_generator (d := fun p : ℕ × F.Desc => p.2) (by fun_prop))
    · exact ComputableInPolyTime.const false
  guess := (ComputableInPolyTime.const true).isPPTOn

-- Against a corrupted receiver, the advantage is the DDH advantage of an explicit reduction plus
-- `6 / 2 ^ n`.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (Z : Environment F.ddhOTFamily {1})
    (n : ℕ) :
    Game.advantage (F.ddhOTFamily.realGame setup {1} Z n)
        (F.ddhOTFamily.idealGame setup {1}
          (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 6 / 2 ^ n :=
  F.advantage_ddhOTReceiverGame_le setup Z n

-- Under DDH, every PPT receiver-corrupting environment has negligible advantage against the
-- exact-sampling simulator: the reduction's certificate lets `F.DDH setup` apply to it.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup)
    (Z : Environment F.ddhOTFamily {1}) (hZ : Z.IsPPT F.ddhOTEncoding) :
    Negligible fun n => Game.advantage (F.ddhOTFamily.realGame setup {1} Z n)
      (F.ddhOTFamily.idealGame setup {1}
        (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n) := by
  have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hZ)
  negligible using F.advantage_ddhOTReceiverGame_le setup Z

end CslibFrontierTests.Crypto.DDHOTFamily
