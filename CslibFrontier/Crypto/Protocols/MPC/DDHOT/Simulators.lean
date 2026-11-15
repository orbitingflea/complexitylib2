/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Tactic.Negligible

/-!
# Semi-honest security of DDH oblivious transfer with PPT simulators

`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Family.lean` runs
`Cslib.Crypto.Protocols.MPC.ddhOTProtocol` over a `PrimeOrderGroupFamily` `F` as the protocol
family `ddhOTFamily`, with the encoding `ddhOTEncoding`, and reduces a corrupted receiver to DDH
against the exact-sampling simulator `ddhOTReceiverSim`. The exact-sampling simulators
`ddhOTSenderSim` and `ddhOTReceiverSim` draw exact uniform exponents in `ZMod (F.order d)`, which
no bounded-time fair-coin machine can do for an odd prime order. This module gives simulator
families that run the same algorithms (`ddhOTSenderSimWithCoins`, `ddhOTReceiverSimWithCoins`)
on six exponents drawn with `sampleExp n d`, the technique of [BonehShoup2023], Remark 23.5
(p. 1059), proves them PPT for `ddhOTEncoding`, and proves that they are statistically within
`6 / 2 ^ n` of the exact-sampling simulators. Under `F.DDH setup`, DDH oblivious transfer is
therefore semi-honest secure against the corruption of either party
(`DDH.ddhOTSemiHonestSecure`), in the sense of
`Cslib.Crypto.Protocols.MPC.ProtocolFamily.SemiHonestSecure`. Against a corrupted sender the
security is statistical: every environment, efficient or not, has advantage at most `6 / 2 ^ n`
(`advantage_ddhOTSenderGame_le`).

## Comparison with [BonehShoup2023], Theorem 23.7

`DDH.ddhOTSemiHonestSecure` is a step towards [BonehShoup2023], Theorem 23.7 (p. 1058), not the
cited result. Its simulators are efficient, as Definition 23.5 (p. 1044) and Section 23.5.2.2
(p. 1043) require, but it differs from the theorem:

* the notion is stand-alone: the environment chooses the inputs and sees the corrupted party's
  view and both outputs after the run, whereas the theorem is stated in the restricted execution
  framework of Section 23.5.6 (p. 1054), in which the environment exchanges messages with the
  parties and the adversary or simulator during the execution;
* only the corruption of exactly one party is covered, whereas the theorem covers every set of
  corrupted parties; the source treats no corruption and full corruption as the cases in which
  there is not much for the simulator to do (p. 1059);
* the honest parties sample exact uniform exponents and their views hold these exponents, whereas
  the source requires the parties' only random objects to be random bit strings (p. 1059);
* the protocol is the variant of Figure 23.17 documented in `DDHOT.lean`, and the setup law is an
  arbitrary distribution on group parameters, as in `F.DDH setup`.

The library's PPT notion `IsPPTOn` is strict: every run halts within a polynomial bound. The
source's compatibility condition (Section 23.5.2.2) bounds the running time only with overwhelming
probability.

## Comparison with [Lindell2017], Definition 4.1

For two parties, [Lindell2017], Section 4.2, Definition 4.1 (p. 7) corresponds to the requirement
of `SemiHonestSecure` for each corrupted party, so `DDH.ddhOTSemiHonestSecure` has the shape of
that definition, up to the differences of the notion listed in
`CslibFrontier/Crypto/Protocols/MPC/Asymptotic.lean` (uniform environments that choose the inputs
after seeing the group parameters, a public setup law). It is still not that definition for DDH
oblivious transfer: in the source the parties run in polynomial time (p. 3) and a party's view
holds the contents of its random tape (p. 7), whereas the honest parties of `ddhOTProtocol` draw
exact uniform exponents and their views hold these exponents. This idealizes the protocol's own
algorithms, as the comparison with Theorem 23.7 above also notes.

## Main definitions

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverSimSampleExp`: the simulator families that draw
  their exponents with `sampleExp`.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTSenderSimSampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverSimSampleExp`: the simulator families are
  PPT for `ddhOTEncoding`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTSenderSimSampleExp_le`,
  `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_ddhOTReceiverSimSampleExp_le`: on every input,
  they are within statistical distance `6 / 2 ^ n` of the exact-sampling simulators.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTSenderGame_le`: against a corrupted sender,
  every environment, efficient or not, has advantage at most `6 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTSemiHonestSecure`: a step towards
  [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies that DDH oblivious
  transfer is semi-honest secure against the corruption of either party.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5 (Section 23.5.2.2, p. 1043; Definition 23.5, p. 1044;
  Section 23.5.6, p. 1054; Theorem 23.7, p. 1058; Remark 23.5, p. 1059).
* [Y. Lindell, *How To Simulate It – A Tutorial on the Simulation Proof Technique*, ECCC
  TR17-112][Lindell2017], Section 2 (p. 3) and Section 4.2 (Definition 4.1, p. 7).
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### The simulator families -/

/-- The simulator family for a corrupted sender that runs the algorithm of `ddhOTSenderSim`,
`ddhOTSenderSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTSenderSimSampleExp : SimulatorFamily F.ddhOTFamily {0} :=
  fun n d xI _ => do
    let a ← F.sampleExp n d
    let r₀ ← F.sampleExp n d
    let s₀ ← F.sampleExp n d
    let r₁ ← F.sampleExp n d
    let s₁ ← F.sampleExp n d
    let b ← F.sampleExp n d
    return ddhOTSenderSimWithCoins (F.generator d) ((a : ZMod (F.order d)),
      (r₀ : ZMod (F.order d)), (s₀ : ZMod (F.order d)), (r₁ : ZMod (F.order d)),
      (s₁ : ZMod (F.order d))) b xI

/-- The simulator family for a corrupted receiver that runs the algorithm of `ddhOTReceiverSim`,
`ddhOTReceiverSimWithCoins`, on six exponents drawn with `sampleExp n d` instead of exact uniform
ones. -/
@[expose] noncomputable def ddhOTReceiverSimSampleExp : SimulatorFamily F.ddhOTFamily {1} :=
  fun n d xI yI => do
    let a ← F.sampleExp n d
    let b ← F.sampleExp n d
    let r ← F.sampleExp n d
    let s ← F.sampleExp n d
    let k ← F.sampleExp n d
    let c ← F.sampleExp n d
    return ddhOTReceiverSimWithCoins (F.generator d) a b r s k c xI yI

/-! ### Statistical closeness to the exact-sampling simulators -/

/-- On every input, no test `k` tells `ddhOTSenderSimSampleExp` from `ddhOTSenderSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTSenderSimSampleExp_le (n : ℕ) (d : F.Desc)
    (xI : (i : ({0} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({0} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({0} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTSenderSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTSenderSimSampleExp n d xI yI)).bind k) ≤ 6 / 2 ^ n := by
  simp only [ddhOTSenderSim, ddhOTSenderSimSampleExp, sampleDDHOTSenderCoins, ProbComp.eval_bind,
    ProbComp.eval_pure, ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_six_le n d fun a r₀ s₀ r₁ s₁ b =>
    k (ddhOTSenderSimWithCoins (F.generator d) (a, r₀, s₀, r₁, s₁) b xI)

/-- On every input, no test `k` tells `ddhOTReceiverSimSampleExp` from `ddhOTReceiverSim` with
advantage more than `6 / 2 ^ n`. -/
theorem advantage_bind_ddhOTReceiverSimSampleExp_le (n : ℕ) (d : F.Desc)
    (xI : (i : ({1} : Finset (Fin 2))) → OTIn (F.Carrier d) i)
    (yI : (i : ({1} : Finset (Fin 2))) → OTOut (F.Carrier d) i)
    (k : ((i : ({1} : Finset (Fin 2))) →
      PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i) →
        Game) :
    Game.advantage ((ProbComp.eval (ddhOTReceiverSim (F.generator d) (F.order d) xI yI)).bind k)
      ((ProbComp.eval (F.ddhOTReceiverSimSampleExp n d xI yI)).bind k) ≤ 6 / 2 ^ n := by
  simp only [ddhOTReceiverSim, ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_pure,
    ProbComp.eval_uniform, PMF.bind_bind, PMF.pure_bind]
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_six_le n d fun a b r s k' c =>
    k (ddhOTReceiverSimWithCoins (F.generator d) a b r s k' c xI yI)

/-! ### Efficiency of the simulator families -/

/-- Six `sampleExp` draws followed by an efficiently computable function of the input and the
draws are uniform strict PPT. -/
private theorem isPPTOn_sampleExp_six {α β : Type} {enc : α ↪ List Bool}
    {encOut : β ↪ List Bool} {n : α → ℕ} {d : α → F.Desc}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc F.encDesc)
    {W : α → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → β}
    (hW : ∀ {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α} {a₁ a₂ a₃ a₄ a₅ a₆ : γ → ℕ},
      ComputableInPolyTime x encγ enc → ComputableInPolyTime a₁ encγ encNat →
      ComputableInPolyTime a₂ encγ encNat → ComputableInPolyTime a₃ encγ encNat →
      ComputableInPolyTime a₄ encγ encNat → ComputableInPolyTime a₅ encγ encNat →
      ComputableInPolyTime a₆ encγ encNat →
      ComputableInPolyTime (fun c => W (x c) (a₁ c) (a₂ c) (a₃ c) (a₄ c) (a₅ c) (a₆ c)) encγ
        encOut) :
    IsPPTOn enc encOut (fun x => do
      let a₁ ← F.sampleExp (n x) (d x)
      let a₂ ← F.sampleExp (n x) (d x)
      let a₃ ← F.sampleExp (n x) (d x)
      let a₄ ← F.sampleExp (n x) (d x)
      let a₅ ← F.sampleExp (n x) (d x)
      let a₆ ← F.sampleExp (n x) (d x)
      pure (W x a₁ a₂ a₃ a₄ a₅ a₆)) := by
  have hsample {γ : Type} {encγ : γ ↪ List Bool} {x : γ → α}
      (hx : ComputableInPolyTime x encγ enc) :
      IsPPTOn encγ encNat fun c => F.sampleExp (n (x c)) (d (x c)) :=
    F.isPPTOn_sampleExp (hn.comp hx) (hd.comp hx)
  refine IsPPTOn.bind_with (hsample .id') ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
  exact (hW (γ := ((((((α × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)) (x := fun p => p.1.1.1.1.1.1)
    (a₁ := fun p => p.1.1.1.1.1.2) (a₂ := fun p => p.1.1.1.1.2) (a₃ := fun p => p.1.1.1.2)
    (a₄ := fun p => p.1.1.2) (a₅ := fun p => p.1.2) (a₆ := fun p => p.2) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)).isPPTOn

/-- The view words that `ddhOTSenderSimSampleExp` writes at group parameters `d` on the sender's
messages `m = (m₀, m₁)` and exponents `a, r₀, s₀, r₁, s₁, b`: the exponents reduced modulo
`q = F.order d`, and the branch keys `b • g` and `a • g + (q - b % q) • g`. -/
private def ddhOTSenderSimWords (d : F.Desc) (m : F.Carrier d × F.Carrier d)
    (a r₀ s₀ r₁ s₁ b : ℕ) : DDHOTSenderViewWords :=
  let q := F.order d
  let g := F.generator d
  ⟨F.encode d m.1, F.encode d m.2, a % q, r₀ % q, s₀ % q, r₁ % q, s₁ % q,
    F.encode d ((b : ZMod q) • g), F.encode d ((a : ZMod q) • g + ((q - b % q : ℕ) : ZMod q) • g)⟩

/-- The party `0` of the coalition `{0}`. -/
private abbrev sender : ({0} : Finset (Fin 2)) := ⟨0, Finset.mem_singleton_self 0⟩

/-- `ddhOTSenderSimSampleExp` is PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTSenderSimSampleExp : F.ddhOTSenderSimSampleExp.IsPPT F.ddhOTEncoding := by
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExp_six
    (n := fun x : SimInput F.ddhOTFamily {0} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime F.ddhOTEncoding .id')
    (encSimInput_desc_polyTime F.ddhOTEncoding .id')
    (W := fun x a r₀ s₀ r₁ s₁ b => encPi encBits fun _ : ({0} : Finset (Fin 2)) =>
      encDDHOTSenderViewWords (F.ddhOTSenderSimWords x.desc (x.inputs sender) a r₀ s₀ r₁ s₁ b))
    fun {γ encγ x _ _ _ _ _ _} hx ha hr₀ hs₀ hr₁ hs₁ hb => ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime F.ddhOTEncoding hx
    have hinputs : ComputableInPolyTime (fun c => fun i : ({0} : Finset (Fin 2)) =>
        F.ddhOTEncoding.input.rep (x c).secParam (x c).desc i ((x c).inputs i)) encγ
        (encDPi fun i : ({0} : Finset (Fin 2)) => F.ddhOTEncoding.input.enc i) :=
      (encSimInput_inputs_polyTime F.ddhOTEncoding hx).of_enc_eq fun _ => rfl
    have hm : ComputableInPolyTime (fun c => (F.encode (x c).desc ((x c).inputs sender).1,
        F.encode (x c).desc ((x c).inputs sender).2)) encγ (encPair encBits encBits) :=
      (ComputableInPolyTime.dpi_apply _ sender).comp hinputs
    have hq := F.computableInPolyTime_order.comp hd
    have hg := computableInPolyTime_encode_generator hd
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTSenderViewWords_mk_polyTime hm.fst' hm.snd'
      (ha.binary_mod' hq) (hr₀.binary_mod' hq) (hs₀.binary_mod' hq) (hr₁.binary_mod' hq)
      (hs₁.binary_mod' hq) (computableInPolyTime_encode_natCast_smul hd hb hg)
      (computableInPolyTime_encode_add hd (computableInPolyTime_encode_natCast_smul hd ha hg)
        (computableInPolyTime_encode_natCast_smul hd (hq.binary_sub' (hb.binary_mod' hq))
          hg))).encoding_comp).encoding_comp
  · simp only [ddhOTSenderSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
      PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun r₀ =>
      congrArg (PMF.bind _) (funext fun s₀ => congrArg (PMF.bind _) (funext fun r₁ =>
        congrArg (PMF.bind _) (funext fun s₁ => congrArg (PMF.bind _) (funext fun b =>
          congrArg PMF.pure ?_))))))
    refine Eq.trans ?_
      (F.ddhOTEncoding.view.encCoalition_singleton x.secParam x.desc 0 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTSenderViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    change _ = F.ddhOTSenderViewWords d (ddhOTSenderView (xs sender)
      ((a : ZMod q), (r₀ : ZMod q), (s₀ : ZMod q), (r₁ : ZMod q), (s₁ : ZMod q))
      ((b : ZMod q) • g, (a : ZMod q) • g - (b : ZMod q) • g))
    simp only [ddhOTSenderSimWords, ddhOTSenderViewWords, ddhOTSenderView,
      ZMod.natCast_sub_mod_eq_neg, neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
    rfl

/-- The view words that `ddhOTReceiverSimSampleExp` writes at group parameters `d` on the choice
bit `σ`, the receiver's output `m` and exponents `a, b, r, s, k, c`: the coin reduced modulo
`F.order d`, the first message `a • g`, and the branches `(e, b • e + m)` with
`e = r • g + s • (a • g)` and `(k • g, c • g)`, in the order given by the choice bit. -/
private def ddhOTReceiverSimWords (d : F.Desc) (σ : Bool) (m : F.Carrier d) (a b r s k c : ℕ) :
    DDHOTReceiverViewWords :=
  let q := F.order d
  let g := F.generator d
  let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
  let chosen₁ := F.encode d e
  let chosen₂ := F.encode d ((b : ZMod q) • e + m)
  let other₁ := F.encode d ((k : ZMod q) • g)
  let other₂ := F.encode d ((c : ZMod q) • g)
  ⟨σ, b % q, F.encode d ((a : ZMod q) • g), if σ then other₁ else chosen₁,
    if σ then other₂ else chosen₂, if σ then chosen₁ else other₁, if σ then chosen₂ else other₂⟩

/-- The party `1` of the coalition `{1}`. -/
private abbrev receiver : ({1} : Finset (Fin 2)) := ⟨1, Finset.mem_singleton_self 1⟩

/-- `ddhOTReceiverSimSampleExp` is PPT for `ddhOTEncoding`. -/
theorem isPPT_ddhOTReceiverSimSampleExp : F.ddhOTReceiverSimSampleExp.IsPPT F.ddhOTEncoding := by
  refine isPPTOn_iff_encoded.mpr ((F.isPPTOn_sampleExp_six
    (n := fun x : SimInput F.ddhOTFamily {1} => x.secParam) (d := fun x => x.desc)
    (encSimInput_secParam_polyTime F.ddhOTEncoding .id')
    (encSimInput_desc_polyTime F.ddhOTEncoding .id')
    (W := fun x a b r s k c => encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
      encDDHOTReceiverViewWords
        (F.ddhOTReceiverSimWords x.desc (x.inputs receiver) (x.outputs receiver) a b r s k c))
    fun {γ encγ x _ _ _ _ _ _} hx ha hb hr hs hk hc => ?_).congr fun x => ?_)
  · have hd : ComputableInPolyTime (fun c => (x c).desc) encγ F.encDesc :=
      encSimInput_desc_polyTime F.ddhOTEncoding hx
    have hinputs : ComputableInPolyTime (fun c => fun i : ({1} : Finset (Fin 2)) =>
        F.ddhOTEncoding.input.rep (x c).secParam (x c).desc i ((x c).inputs i)) encγ
        (encDPi fun i : ({1} : Finset (Fin 2)) => F.ddhOTEncoding.input.enc i) :=
      (encSimInput_inputs_polyTime F.ddhOTEncoding hx).of_enc_eq fun _ => rfl
    have houtputs : ComputableInPolyTime (fun c => fun i : ({1} : Finset (Fin 2)) =>
        F.ddhOTEncoding.output.rep (x c).secParam (x c).desc i ((x c).outputs i)) encγ
        (encDPi fun i : ({1} : Finset (Fin 2)) => F.ddhOTEncoding.output.enc i) :=
      (encSimInput_outputs_polyTime F.ddhOTEncoding hx).of_enc_eq fun _ => rfl
    have hσ : ComputableInPolyTime (fun c => ((x c).inputs receiver : Bool)) encγ encBool :=
      (ComputableInPolyTime.dpi_apply _ receiver).comp hinputs
    have hm : ComputableInPolyTime (fun c => F.encode (x c).desc ((x c).outputs receiver)) encγ
        encBits :=
      (ComputableInPolyTime.dpi_apply _ receiver).comp houtputs
    have hg := computableInPolyTime_encode_generator hd
    have hu := computableInPolyTime_encode_natCast_smul hd ha hg
    have he := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hr hg)
      (computableInPolyTime_encode_natCast_smul hd hs hu)
    have hbody := computableInPolyTime_encode_add hd
      (computableInPolyTime_encode_natCast_smul hd hb he) hm
    have hk' := computableInPolyTime_encode_natCast_smul hd hk hg
    have hc' := computableInPolyTime_encode_natCast_smul hd hc hg
    exact (ComputableInPolyTime.pi fun _ => (encDDHOTReceiverViewWords_mk_polyTime hσ
      (hb.binary_mod' (F.computableInPolyTime_order.comp hd)) hu (hσ.ite' hk' he)
      (hσ.ite' hc' hbody) (hσ.ite' he hk') (hσ.ite' hbody hc')).encoding_comp).encoding_comp
  · simp only [ddhOTReceiverSimSampleExp, ProbComp.eval_bind, ProbComp.eval_map,
      ProbComp.eval_pure, PMF.map_bind, PMF.pure_map]
    refine congrArg (PMF.bind _) (funext fun a => congrArg (PMF.bind _) (funext fun b =>
      congrArg (PMF.bind _) (funext fun r => congrArg (PMF.bind _) (funext fun s =>
        congrArg (PMF.bind _) (funext fun k => congrArg (PMF.bind _) (funext fun c =>
          congrArg PMF.pure ?_))))))
    refine Eq.trans ?_
      (F.ddhOTEncoding.view.encCoalition_singleton x.secParam x.desc 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTReceiverViewWords ?_)
    obtain ⟨n, d, xs, ys⟩ := x
    let q := F.order d
    let g := F.generator d
    dsimp only
    simp only [ddhOTReceiverSimWithCoins]
    obtain ⟨σ, hσ⟩ : ∃ σ : Bool, xs receiver = σ := ⟨_, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m : F.Carrier d, ys receiver = m := ⟨_, rfl⟩
    rw [hσ, hm]
    let e := (r : ZMod q) • g + (s : ZMod q) • (a : ZMod q) • g
    change _ = F.ddhOTReceiverViewWords d (ddhOTReceiverView σ (b : ZMod q) ((a : ZMod q) • g)
      (if σ then (((k : ZMod q) • g, (c : ZMod q) • g), (e, (b : ZMod q) • e + m))
        else ((e, (b : ZMod q) • e + m), ((k : ZMod q) • g, (c : ZMod q) • g))))
    cases σ <;> simp only [ddhOTReceiverSimWords, ddhOTReceiverViewWords, ddhOTReceiverView,
      Bool.false_eq_true, ↓reduceIte, ZMod.val_natCast] <;> rfl

/-! ### Security -/

/-- **Statistical security against a corrupted sender**: for every environment, with no efficiency
requirement, the advantage between the real game and the ideal game with
`ddhOTSenderSimSampleExp` is at most `6 / 2 ^ n`. The real game is the ideal game with the
exact-sampling simulator `ddhOTSenderSim` (`idealJoint_ddhOT_sender`). -/
theorem advantage_ddhOTSenderGame_le (setup : ℕ → PMF F.Desc) (Z : Environment F.ddhOTFamily {0})
    (n : ℕ) :
    Game.advantage (F.ddhOTFamily.realGame setup {0} Z n)
      (F.ddhOTFamily.idealGame setup {0} F.ddhOTSenderSimSampleExp Z n) ≤ 6 / 2 ^ n := by
  rw [ProtocolFamily.realGame_eq_idealGame
    (S := fun _ d => ddhOTSenderSim (F.generator d) (F.order d))
    (fun _ d => idealJoint_ddhOT_sender _ _)]
  exact ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTSenderSimSampleExp_le n) Z

/-- A step towards [BonehShoup2023], Theorem 23.7, not the cited result: `F.DDH setup` implies
that DDH oblivious transfer is semi-honest secure against a corrupted sender (`{0}`) and against a
corrupted receiver (`{1}`), for the encoding `ddhOTEncoding` (`ProtocolFamily.SemiHonestSecure`).
The simulators are `ddhOTSenderSimSampleExp` and `ddhOTReceiverSimSampleExp`, certified by
`isPPT_ddhOTSenderSimSampleExp` and `isPPT_ddhOTReceiverSimSampleExp`. The theorem is stated in
the restricted execution framework of Section 23.5.6, covers every set of corrupted parties, and
has the parties derive their exponents from random bit strings; the module documentation lists
these and the other differences. The only premise is `F.DDH setup`; the reduction is certified by
`isPPT_ddhOTReceiverToDDHDistinguisher`. -/
theorem DDH.ddhOTSemiHonestSecure {F : PrimeOrderGroupFamily} {setup : ℕ → PMF F.Desc}
    (hDDH : F.DDH setup) :
    F.ddhOTFamily.SemiHonestSecure setup {0} F.ddhOTEncoding ∧
      F.ddhOTFamily.SemiHonestSecure setup {1} F.ddhOTEncoding := by
  refine ⟨⟨F.ddhOTSenderSimSampleExp, F.isPPT_ddhOTSenderSimSampleExp, fun Z _ => ?_⟩,
    ⟨F.ddhOTReceiverSimSampleExp, F.isPPT_ddhOTReceiverSimSampleExp, fun Z hZ => ?_⟩⟩
  · negligible using F.advantage_ddhOTSenderGame_le setup Z
  · have hB := hDDH _ (F.isPPT_ddhOTReceiverToDDHDistinguisher hZ)
    have h (n : ℕ) : Game.advantage (F.ddhOTFamily.realGame setup {1} Z n)
        (F.ddhOTFamily.idealGame setup {1} F.ddhOTReceiverSimSampleExp Z n) ≤
          Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
            (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 6 / 2 ^ n +
            6 / 2 ^ n :=
      (Game.advantage_triangle _ _ _).trans (add_le_add
        (F.advantage_ddhOTReceiverGame_le setup Z n)
        (ProtocolFamily.advantage_idealGame_le (F.advantage_bind_ddhOTReceiverSimSampleExp_le n) Z))
    negligible using h

end Cslib.Crypto.PrimeOrderGroupFamily
