/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.Advantage
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Negligible.Basic

/-! # Asymptotic semi-honest security: a refuted and a satisfied instance

Clients of `CslibFrontier.Crypto.Protocols.MPC.Asymptotic` under module encapsulation. In
`sendProtocol reveal`, party 0 sends its input bit to party 1; party 0 outputs its input, and
party 1 outputs the received bit when `reveal` holds and `false` otherwise.

* With `reveal = false` the functionality gives party 1 only `false`, so the protocol leaks party
  0's bit. `not_semiHonestSecure_send_false` refutes `SemiHonestSecure` against a corrupted party
  1 with the PPT environment `compareEnvironment`, which reads the corrupted party's view from
  `encGuessInput`: it accepts in every real run and with probability `1 / 2` in every ideal run,
  whatever the simulator.
* With `reveal = true` the functionality gives party 1 the bit, and
  `semiHonestSecure_send_true` proves `SemiHonestSecure` unconditionally through
  `SemiHonestSecure.of_perfect`, with the PPT simulator `sendSimulator`. -/

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.Protocols.MPC Turing.MultiTapeTM
open scoped NNReal

public section

namespace CslibFrontierTests.Crypto.MPCAsymptotic

/-- One round: party 0 sends a bit to party 1. -/
abbrev sendSchedule : Schedule 2 noOracleSpec := [.message 0 1 Bool]

/-- Party 0 sends its input bit to party 1. Party 0 outputs its input; party 1 outputs the received
bit when `reveal` holds, and `false` otherwise. -/
def sendProtocol (reveal : Bool) :
    Protocol 2 noOracleSpec sendSchedule (fun _ => Bool) (fun _ => Unit) (fun _ => Bool) where
  sampleCoins _ := pure ()
  steps := .message (sender := 0) (receiver := 1) (fun st => st.1)
    (.done fun i st => if h : i = 1 then reveal && st.2 h else st.1.1)

/-- The functionality of `sendProtocol reveal`: party 0 gets its input back, and party 1 gets party
0's input when `reveal` holds and `false` otherwise. -/
def sendFunctionality (reveal : Bool) : Functionality 2 (fun _ => Bool) (fun _ => Bool) :=
  .ofDeterministic fun x i => if i = 1 then reveal && x 0 else x 0

/-- `sendProtocol reveal` as a protocol family that ignores the security parameter and has no
public parameters. -/
abbrev sendFamily (reveal : Bool) : ProtocolFamily 2 where
  Desc := Unit
  spec _ _ := noOracleSpec
  sc _ _ := sendSchedule
  In _ _ _ := Bool
  Coins _ _ _ := Unit
  Out _ _ _ := Bool
  protocol _ _ := sendProtocol reveal
  world _ _ := noOracleWorld
  functionality _ _ := sendFunctionality reveal

/-- A party's view as two bits: its input and the bit it received (`false` for party 0). -/
def viewBits (i : Fin 2) (v : PartyView (fun _ => Bool) (fun _ => Unit) sendSchedule i) :
    Bool × Bool :=
  (v.input, if h : i = 1 then v.received.1 h else false)

theorem viewBits_injective (i : Fin 2) : Function.Injective (viewBits i) := by
  rintro ⟨x, ⟨⟩, r, ⟨⟩⟩ ⟨x', ⟨⟩, r', ⟨⟩⟩ h
  simp only [viewBits, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  have hr : r = r' := funext fun hi => by subst hi; exact h
  rw [hr]

/-- Bits as themselves, and views as `viewBits`. -/
def sendEncoding (reveal : Bool) : (sendFamily reveal).Encoding where
  desc := encUnit
  input := { Rep := fun _ => Bool, enc := fun _ => encBool, rep := fun _ _ _ => .refl Bool }
  output := { Rep := fun _ => Bool, enc := fun _ => encBool, rep := fun _ _ _ => .refl Bool }
  view :=
    { Rep := fun _ => Bool × Bool, enc := fun _ => encPair encBool encBool
      rep := fun _ _ i => ⟨viewBits i, viewBits_injective i⟩ }

/-- The trivial setup law. -/
noncomputable def noSetup : ℕ → PMF Unit := fun _ => PMF.pure ()

/-! ### A refuted instance -/

/-- Party 0's input `b` and party 1's input `false`. -/
def sendInputs (b : Bool) : (i : Fin 2) → Bool := fun i => if i = 0 then b else false

/-- The environment that gives party 0 a uniform bit and accepts when the bit that party 1 received
equals party 0's output. -/
noncomputable def compareEnvironment : Environment (sendFamily false) {1} where
  choose _ _ := do
    let b ← ProbComp.uniform Bool
    return ⟨sendInputs b, []⟩
  guess _ _ _ := fun (v, y) =>
    pure (decide ((v ⟨1, Finset.mem_singleton_self 1⟩).received.1 rfl = y 0))

/-- Party 1 of the coalition `{1}`. -/
abbrev receiver : ({1} : Finset (Fin 2)) := ⟨1, Finset.mem_singleton_self 1⟩

/-- `compareEnvironment` is PPT: it samples one bit, and it reads two bits of its input. -/
theorem isPPT_compareEnvironment : compareEnvironment.IsPPT (sendEncoding false) where
  choose := by
    refine ((isPPTOn_uniform_bool _).map (f := fun b =>
      ((fun i => (sendEncoding false).input.rep 0 () i (sendInputs b i)), ([] : List Bool)))
      (ComputableInPolyTime.of_finite _)).congr fun _ => ?_
    simp only [compareEnvironment, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    rfl
  guess := by
    have hviews : ComputableInPolyTime (fun y : GuessInput (sendFamily false) {1} =>
        fun i : ({1} : Finset (Fin 2)) =>
          (sendEncoding false).view.rep y.secParam y.desc i (y.views i))
        (encGuessInput (sendEncoding false))
        (encDPi fun i : ({1} : Finset (Fin 2)) => (sendEncoding false).view.enc i) :=
      (encGuessInput_views_polyTime (sendEncoding false) .id').of_enc_eq fun _ => rfl
    have houtputs : ComputableInPolyTime (fun y : GuessInput (sendFamily false) {1} =>
        fun i => (sendEncoding false).output.rep y.secParam y.desc i (y.outputs i))
        (encGuessInput (sendEncoding false)) (encDPi (sendEncoding false).output.enc) :=
      (encGuessInput_outputs_polyTime (sendEncoding false) .id').of_enc_eq fun _ => rfl
    have hreceived : ComputableInPolyTime (fun y : GuessInput (sendFamily false) {1} =>
        (y.views ⟨1, Finset.mem_singleton_self 1⟩).received.1 rfl)
        (encGuessInput (sendEncoding false)) encBool :=
      ((ComputableInPolyTime.dpi_apply _ receiver).comp hviews).snd'
    have houtput : ComputableInPolyTime (fun y : GuessInput (sendFamily false) {1} => y.outputs 0)
        (encGuessInput (sendEncoding false)) encBool :=
      (ComputableInPolyTime.dpi_apply _ 0).comp houtputs
    exact ((ComputableInPolyTime.of_finite (encIn := encPair encBool encBool)
      (fun p : Bool × Bool => decide (p.1 = p.2))).comp (hreceived.prod houtput)).isPPTOn

/-- Every real run of `compareEnvironment` accepts. -/
theorem realGame_compareEnvironment (n : ℕ) :
    (sendFamily false).realGame noSetup {1} compareEnvironment n = PMF.pure true := by
  simp only [ProtocolFamily.realGame, noSetup, compareEnvironment, PMF.monad_bind_eq_bind,
    PMF.pure_bind, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform]
  refine (congrArg (PMF.bind _) (funext fun b => ?_)).trans (PMF.bind_const _ _)
  simp [Protocol.realJoint, sendProtocol, Protocol.evalWith_eq, OracleComp.pi_succ,
    OracleComp.pi_zero, Steps.evalWith_message, Steps.evalWith_done, Round.deliverMessage,
    Protocol.outputOfView, Steps.outputAt]

/-- Comparing a fixed bit with a uniform bit gives a uniform bit. -/
theorem uniform_bind_decide_eq (r : Bool) :
    ((PMF.uniformOfFintype Bool).bind fun a => PMF.pure (decide (r = a))) =
      PMF.uniformOfFintype Bool := by
  ext c
  cases r <;> cases c <;> simp [PMF.bind_apply, PMF.uniformOfFintype_apply]

/-- Every ideal run of `compareEnvironment` accepts with probability `1 / 2`, whatever the
simulator: the simulator sees party 1's input and output, which do not depend on party 0's bit. -/
theorem idealGame_compareEnvironment (S : SimulatorFamily (sendFamily false) {1}) (n : ℕ) :
    (sendFamily false).idealGame noSetup {1} S compareEnvironment n =
      PMF.uniformOfFintype Bool := by
  simp only [ProtocolFamily.idealGame, noSetup, compareEnvironment, PMF.monad_bind_eq_bind,
    PMF.pure_bind, ProbComp.eval_bind, ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind,
    eval_idealJoint, sendFunctionality, Functionality.ofDeterministic, PMF.bind_map]
  have hx (a : Bool) : ({1} : Finset (Fin 2)).restrict (sendInputs a) = fun _ => false := by
    funext ⟨i, hi⟩
    obtain rfl := Finset.mem_singleton.mp hi
    rfl
  have hy (a : Bool) : ({1} : Finset (Fin 2)).restrict
      (fun i => if i = 1 then false && sendInputs a 0 else sendInputs a 0) = fun _ => false := by
    funext ⟨i, hi⟩
    obtain rfl := Finset.mem_singleton.mp hi
    rfl
  have h0 (a : Bool) :
      (if (0 : Fin 2) = 1 then false && sendInputs a 0 else sendInputs a 0) = a := rfl
  simp only [hx, hy, Function.comp_def, h0]
  rw [PMF.bind_comm]
  simp only [uniform_bind_decide_eq, PMF.bind_const]

/-- The leaky protocol is not semi-honest secure against a corrupted party 1. -/
theorem not_semiHonestSecure_send_false :
    ¬ (sendFamily false).SemiHonestSecure noSetup {1} (sendEncoding false) := by
  rintro ⟨S, -, hind⟩
  have h := hind compareEnvironment isPPT_compareEnvironment
  simp only [realGame_compareEnvironment, idealGame_compareEnvironment] at h
  refine not_negligible_const ?_ h
  rw [Ne, nndist_eq_zero]
  intro heq
  have h2 := congrArg (fun x : ℝ≥0 => (x : ℝ)) heq
  norm_num [Game.succProbability, PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat] at h2

/-! ### A satisfied instance -/

/-- The simulator for a corrupted party 1 of `sendProtocol true`: the view with party 1's input
and, as the received bit, party 1's output. -/
def sendSimulator : SimulatorFamily (sendFamily true) {1} := fun _ _ xI yI =>
  pure (singletonView (⟨xI ⟨1, Finset.mem_singleton_self 1⟩, (),
    (fun _ => yI ⟨1, Finset.mem_singleton_self 1⟩, ())⟩ :
      PartyView (fun _ => Bool) (fun _ => Unit) sendSchedule 1))

/-- `sendSimulator` is PPT: it copies two bits. -/
theorem isPPT_sendSimulator : sendSimulator.IsPPT (sendEncoding true) := by
  have hinputs : ComputableInPolyTime (fun x : SimInput (sendFamily true) {1} =>
      fun i : ({1} : Finset (Fin 2)) =>
        (sendEncoding true).input.rep x.secParam x.desc i (x.inputs i))
      (encSimInput (sendEncoding true))
      (encDPi fun i : ({1} : Finset (Fin 2)) => (sendEncoding true).input.enc i) :=
    (encSimInput_inputs_polyTime (sendEncoding true) .id').of_enc_eq fun _ => rfl
  have houtputs : ComputableInPolyTime (fun x : SimInput (sendFamily true) {1} =>
      fun i : ({1} : Finset (Fin 2)) =>
        (sendEncoding true).output.rep x.secParam x.desc i (x.outputs i))
      (encSimInput (sendEncoding true))
      (encDPi fun i : ({1} : Finset (Fin 2)) => (sendEncoding true).output.enc i) :=
    (encSimInput_outputs_polyTime (sendEncoding true) .id').of_enc_eq fun _ => rfl
  have hin : ComputableInPolyTime (fun x : SimInput (sendFamily true) {1} => x.inputs receiver)
      (encSimInput (sendEncoding true)) encBool :=
    (ComputableInPolyTime.dpi_apply _ receiver).comp hinputs
  have hout : ComputableInPolyTime (fun x : SimInput (sendFamily true) {1} => x.outputs receiver)
      (encSimInput (sendEncoding true)) encBool :=
    (ComputableInPolyTime.dpi_apply _ receiver).comp houtputs
  have hwords : ComputableInPolyTime (fun x : SimInput (sendFamily true) {1} =>
      encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
        encPair encBool encBool (x.inputs receiver, x.outputs receiver))
      (encSimInput (sendEncoding true)) encBits :=
    (ComputableInPolyTime.pi fun _ =>
      ComputableInPolyTime.encoding_comp (ComputableInPolyTime.prod hin hout)).encoding_comp
  refine isPPTOn_iff_encoded.mpr (hwords.isPPTOn.congr fun x => ?_)
  simp only [sendSimulator, ProbComp.eval_pure, ProbComp.eval_map, PMF.pure_map]
  refine congrArg PMF.pure (Eq.trans ?_
    ((sendEncoding true).view.encCoalition_singleton x.secParam x.desc 1
      (singletonView (⟨x.inputs receiver, (), (fun _ => x.outputs receiver, ())⟩ :
        PartyView (fun _ => Bool) (fun _ => Unit) sendSchedule 1))).symm)
  rfl

/-- `sendSimulator` simulates a corrupted party 1 perfectly. -/
theorem idealJoint_sendSimulator (n : ℕ) (d : Unit) (x : (i : Fin 2) → Bool) :
    ProbComp.eval (idealJoint (sendFunctionality true) {1} (sendSimulator n d) x) =
      (sendProtocol true).realJoint noOracleWorld {1} x := by
  simp only [Fin.isValue, idealJoint, sendFunctionality, Functionality.ofDeterministic,
    Bool.true_and, ite_self, sendSimulator, Finset.restrict, bind_pure_comp, map_pure,
    ProbComp.eval_pure, Protocol.realJoint, sendProtocol, Protocol.evalWith_eq, OracleComp.pi_succ,
    Nat.reduceAdd, OracleComp.pi_zero, Protocol.outputOfView, Steps.outputAt,
    Steps.evalWith_message, Steps.evalWith_done, PMF.pure_map, Round.deliverMessage, dite_eq_ite,
    PMF.pure_bind, Prod.map_apply, id_eq]
  congr 1
  refine Prod.ext ?_ (funext fun i => ?_)
  · rw [restrict_singleton]
    rfl
  · fin_cases i <;> rfl

/-- The non-leaky protocol is semi-honest secure against a corrupted party 1, with no
assumption. -/
theorem semiHonestSecure_send_true :
    (sendFamily true).SemiHonestSecure noSetup {1} (sendEncoding true) :=
  ProtocolFamily.SemiHonestSecure.of_perfect isPPT_sendSimulator idealJoint_sendSimulator

end CslibFrontierTests.Crypto.MPCAsymptotic
