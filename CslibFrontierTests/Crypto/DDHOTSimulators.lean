/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators

/-! # Semi-honest security of DDH oblivious transfer: module clients

Clients of `CslibFrontier.Crypto.Protocols.MPC.DDHOT.Simulators` under module encapsulation:
* the encoded words of a simulator's input, and of a receiver's view words;
* the PPT certificates of the `sampleExp` simulator families, and the predicate
  `SimulatorFamily.IsPPT` introduced from a machine certificate and consumed as one;
* the statistical distance of the `sampleExp` simulators from the exact-sampling ones, and the
  ideal games they give through `ProtocolFamily.advantage_idealGame_le`;
* `DDH.ddhOTSemiHonestSecure`, unfolded to its witnesses. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC
  Cslib.Crypto.PrimeOrderGroupFamily Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.DDHOTSimulators

-- The encoded words of a simulator's input: the unary security parameter, the group parameters
-- and the words of the coalition's inputs and outputs, all but the last framed.
example (F : PrimeOrderGroupFamily) (x : SimInput F.ddhOTFamily {1}) :
    encSimInput F.ddhOTEncoding x =
      encPair encUnary (encPair F.encDesc (encPair encBits encBits))
        (x.secParam, x.desc, F.ddhOTEncoding.input.encCoalition x.secParam x.desc {1} x.inputs,
          F.ddhOTEncoding.output.encCoalition x.secParam x.desc {1} x.outputs) :=
  encSimInput_apply _ x

-- The encoded words of a receiver's view.
example (w : DDHOTReceiverViewWords) :
    encDDHOTReceiverViewWords w =
      encPair encBool (encPair encNat (encPair encBits (encPair encBits (encPair encBits
        (encPair encBits encBits)))))
        (w.choiceBit, w.coin, w.firstMessage, w.ephemeral₀, w.body₀, w.ephemeral₁, w.body₁) :=
  encDDHOTReceiverViewWords_apply w

-- The words of a receiver's view determine it.
example (F : PrimeOrderGroupFamily) (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) :=
  F.ddhOTReceiverViewWords_injective d

-- Both `sampleExp` simulator families are PPT.
example (F : PrimeOrderGroupFamily) :
    F.ddhOTSenderSimSampleExp.IsPPT F.ddhOTEncoding ∧
      F.ddhOTReceiverSimSampleExp.IsPPT F.ddhOTEncoding :=
  ⟨F.isPPT_ddhOTSenderSimSampleExp, F.isPPT_ddhOTReceiverSimSampleExp⟩

-- Introducing the predicate: a sender simulator family with the same output laws as
-- `ddhOTSenderSimSampleExp` is PPT, through the latter's machine certificate.
example (F : PrimeOrderGroupFamily) (S : SimulatorFamily F.ddhOTFamily {0})
    (hS : ∀ n d xI yI,
      ProbComp.eval (S n d xI yI) = ProbComp.eval (F.ddhOTSenderSimSampleExp n d xI yI)) :
    S.IsPPT F.ddhOTEncoding :=
  IsPPTOn.congr F.isPPT_ddhOTSenderSimSampleExp fun x => by
    simp only [ProbComp.eval_map, hS]

-- Consuming the predicate: the receiver simulator family that `DDH.ddhOTSemiHonestSecure`
-- provides writes view words of polynomially bounded length.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ (S : SimulatorFamily F.ddhOTFamily {1}) (c d : ℕ), ∀ (x : SimInput F.ddhOTFamily {1}) v,
      v ∈ (ProbComp.eval (S x.secParam x.desc x.inputs x.outputs)).support →
      (F.ddhOTEncoding.view.encCoalition x.secParam x.desc {1} v).length ≤
        c * ((encSimInput F.ddhOTEncoding x).length + 1) ^ d := by
  obtain ⟨S, hS, -⟩ := hDDH.ddhOTSemiHonestSecure.2
  obtain ⟨c, d, h⟩ := IsPPTOn.length_le hS
  exact ⟨S, c, d, fun x v hv => h x _ (by
    simpa only [ProbComp.eval_map, PMF.support_map] using Set.mem_image_of_mem _ hv)⟩

-- Against a corrupted receiver, the ideal games with the exact-sampling and the `sampleExp`
-- simulators differ by at most `6 / 2 ^ n`, for every environment.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (Z : Environment F.ddhOTFamily {1})
    (n : ℕ) :
    Game.advantage
        (F.ddhOTFamily.idealGame setup {1}
          (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n)
        (F.ddhOTFamily.idealGame setup {1} F.ddhOTReceiverSimSampleExp Z n) ≤ 6 / 2 ^ n :=
  ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTReceiverSimSampleExp_le n) Z

-- Under DDH, DDH oblivious transfer is semi-honest secure against either corrupted party.
example (F : PrimeOrderGroupFamily) (setup : ℕ → PMF F.Desc) (hDDH : F.DDH setup) :
    ∃ S : SimulatorFamily F.ddhOTFamily {0}, S.IsPPT F.ddhOTEncoding ∧
      Game.Indistinguishable (F.ddhOTFamily.realGame setup {0})
        (F.ddhOTFamily.idealGame setup {0} S) (Environment.IsPPT F.ddhOTEncoding) :=
  hDDH.ddhOTSemiHonestSecure.1

end CslibFrontierTests.Crypto.DDHOTSimulators
