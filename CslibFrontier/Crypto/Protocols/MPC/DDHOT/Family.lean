/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Protocols.MPC.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.DDHOT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Computational.DiffieHellman.SampleExp
import CslibFrontier.Tactic.PMFSwap

/-!
# DDH oblivious transfer as a protocol family, and its reduction to DDH

`Cslib.Crypto.Protocols.MPC.ddhOTProtocol` is a three-message 1-out-of-2 oblivious transfer over
a group of prime order, a variant of the protocol of [BonehShoup2023], Section 23.5.7, Figure 23.17
(p. 1057). `CslibFrontier/Crypto/Protocols/MPC/DDHOT.lean` defines it, lists its differences from
Figure 23.17, and relates it to the DDH experiment in one fixed group. This module runs it in the
groups of a `PrimeOrderGroupFamily` `F` as the protocol family `ddhOTFamily`
(`Cslib.Crypto.Protocols.MPC.ProtocolFamily`), with the encoding `ddhOTEncoding` for machines,
and reduces a corrupted receiver to DDH.
`CslibFrontier/Crypto/Protocols/MPC/DDHOT/Simulators.lean` gives PPT simulators and proves
semi-honest security (`Cslib.Crypto.PrimeOrderGroupFamily.DDH.ddhOTSemiHonestSecure`).

`ddhOTEncoding` writes group parameters with `F.encDesc` and group elements as `F.encode d` words.
The sender's input is the pair of words of its two messages and the receiver's input is its choice
bit; the sender's output `()` is the empty word and the receiver's output is the word of its
message. A corrupted party's view is written as its view words (`ddhOTSenderViewWords`,
`ddhOTReceiverViewWords`): the group elements as words and the exponents as their values below the
group order. The words determine the view (`ddhOTSenderViewWords_injective`,
`ddhOTReceiverViewWords_injective`).

**Proof of the reduction.** Against a corrupted receiver, `ddhOTReceiverToDDHDistinguisher` turns
an environment `Z` into a DDH distinguisher. It runs `Z`'s input choice, draws the receiver's coin
and the chosen branch's coins with `sampleExp`, and embeds the DDH triple into the unchosen branch
as `Cslib.Crypto.Protocols.MPC.ddhOTReductionWithCoins` does. With exact uniform coins, the real
DDH game would be the real game (`Cslib.Crypto.Protocols.MPC.real_receiver_eq_ddhRealExperiment`),
and the random DDH game would be the ideal game with the exact-sampling simulator `ddhOTReceiverSim`
(`Cslib.Crypto.Protocols.MPC.ideal_receiver_eq_ddhRandomExperiment`). The three approximate draws
cost at most `3 / 2 ^ n` on each side (`advantage_bind_sampleExp_triple_le`), which gives
`advantage_ddhOTReceiverGame_le`. `isPPT_ddhOTReceiverToDDHDistinguisher` proves that the reduction
is PPT whenever `Z` is.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.DDHOTSenderViewWords`,
  `Cslib.Crypto.Protocols.MPC.DDHOTReceiverViewWords`, their encodings, and
  `Cslib.Crypto.Protocols.MPC.DDHOTViewWords`: a party's view as words.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTFamily`: `ddhOTProtocol` over the groups of `F`.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderViewWords`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverViewWords`: the words of a party's view.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTEncoding`: the encoding of the family for machines.
* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverToDDHDistinguisher`: the reduction to DDH.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTSenderViewWords_injective`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddhOTReceiverViewWords_injective`: the words determine the
  view.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_ddhOTReceiverGame_le`: the advantage of an
  environment against a corrupted receiver and the exact-sampling simulator is at most the DDH
  advantage of the reduction plus `6 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_ddhOTReceiverToDDHDistinguisher`: the reduction is
  PPT.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.5.7 (Figure 23.17, p. 1057; Remark 23.5, p. 1059).
-/

public section

namespace Cslib.Crypto.Protocols.MPC

open Turing.MultiTapeTM

/-! ### Views as words -/

/-- The words of a corrupted sender's view in `ddhOTProtocol`: its two messages, its five
exponents `a, r₀, s₀, r₁, s₁` as natural numbers, and the two branch keys of the receiver's
message. -/
structure DDHOTSenderViewWords where
  /-- The word of the message `m₀`. -/
  message₀ : List Bool
  /-- The word of the message `m₁`. -/
  message₁ : List Bool
  /-- The exponent `a` of the first message `u = a • g`. -/
  exponent : ℕ
  /-- The coin `r₀` of branch `0`. -/
  coinR₀ : ℕ
  /-- The coin `s₀` of branch `0`. -/
  coinS₀ : ℕ
  /-- The coin `r₁` of branch `1`. -/
  coinR₁ : ℕ
  /-- The coin `s₁` of branch `1`. -/
  coinS₁ : ℕ
  /-- The word of the branch key `w₀`. -/
  branchKey₀ : List Bool
  /-- The word of the branch key `w₁`. -/
  branchKey₁ : List Bool

/-- The encoding of a sender's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTSenderViewWords : DDHOTSenderViewWords where
  message₀ : encBits, message₁ : encBits, exponent : encNat, coinR₀ : encNat, coinS₀ : encNat,
  coinR₁ : encNat, coinS₁ : encNat, branchKey₀ : encBits, branchKey₁ : encBits

/-- The words of a corrupted receiver's view in `ddhOTProtocol`: its choice bit, its coin `b` as a
natural number, the sender's first message, and the two components of each branch ciphertext of
the sender's reply. -/
structure DDHOTReceiverViewWords where
  /-- The receiver's choice bit `σ`. -/
  choiceBit : Bool
  /-- The receiver's coin `b`. -/
  coin : ℕ
  /-- The word of the sender's first message `u`. -/
  firstMessage : List Bool
  /-- The word of the first component of the ciphertext of branch `0`. -/
  ephemeral₀ : List Bool
  /-- The word of the second component of the ciphertext of branch `0`. -/
  body₀ : List Bool
  /-- The word of the first component of the ciphertext of branch `1`. -/
  ephemeral₁ : List Bool
  /-- The word of the second component of the ciphertext of branch `1`. -/
  body₁ : List Bool

/-- The encoding of a receiver's view words: each field in turn, all but the last framed. -/
enc_structure encDDHOTReceiverViewWords : DDHOTReceiverViewWords where
  choiceBit : encBool, coin : encNat, firstMessage : encBits, ephemeral₀ : encBits,
  body₀ : encBits, ephemeral₁ : encBits, body₁ : encBits

/-- The view words of the two parties of `ddhOTProtocol`: `DDHOTSenderViewWords` for the sender
(party `0`) and `DDHOTReceiverViewWords` for the receiver (party `1`). -/
abbrev DDHOTViewWords : Fin 2 → Type :=
  fun i => Fin.cases (motive := fun _ => Type) DDHOTSenderViewWords
    (fun _ => DDHOTReceiverViewWords) i

end Cslib.Crypto.Protocols.MPC

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM Cslib.Crypto.Protocols.MPC
open scoped NNReal

variable (F : PrimeOrderGroupFamily)

/-! ### The protocol family and its encoding -/

/-- `ddhOTProtocol` over the groups of `F`: at public parameters `d`, the protocol in `F.Carrier d`
with generator `F.generator d`, in the plain model, computing `otFunctionality`. The protocol
depends on the security parameter only through `d`. -/
noncomputable abbrev ddhOTFamily : ProtocolFamily 2 where
  Desc := F.Desc
  spec _ _ := noOracleSpec
  sc _ d := ddhOTSchedule (F.Carrier d)
  In _ d := OTIn (F.Carrier d)
  Coins _ d := DDHOTCoins (F.order d)
  Out _ d := OTOut (F.Carrier d)
  protocol _ d := ddhOTProtocol (F.generator d) (F.order d)
  world _ _ := noOracleWorld
  functionality _ d := otFunctionality (F.Carrier d)

/-- The words of a sender's view in `ddhOTProtocol` over `F.Carrier d`: the messages and branch
keys as `F.encode d` words, and the exponents as their values below `F.order d`. -/
@[expose] def ddhOTSenderViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d))
      0) : DDHOTSenderViewWords :=
  let (m₀, m₁) := view.input
  let (a, r₀, s₀, r₁, s₁) := view.coins
  let (_, w, _) := view.received
  let (w₀, w₁) := w rfl
  ⟨F.encode d m₀, F.encode d m₁, a.val, r₀.val, s₀.val, r₁.val, s₁.val, F.encode d w₀,
    F.encode d w₁⟩

/-- The words of a receiver's view in `ddhOTProtocol` over `F.Carrier d`: the choice bit, the
coin as its value below `F.order d`, and the received group elements as `F.encode d` words. -/
@[expose] def ddhOTReceiverViewWords (d : F.Desc)
    (view : PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d))
      1) : DDHOTReceiverViewWords :=
  let (u, _, reply, _) := view.received
  let ((e₀, c₀), (e₁, c₁)) := reply rfl
  ⟨view.input, view.coins.val, F.encode d (u rfl), F.encode d e₀, F.encode d c₀, F.encode d e₁,
    F.encode d c₁⟩

/-- The words determine a sender's view. -/
theorem ddhOTSenderViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTSenderViewWords d) := by
  rintro ⟨⟨m₀, m₁⟩, ⟨a, r₀, s₀, r₁, s₁⟩, ⟨u, w, reply, ⟨⟩⟩⟩
    ⟨⟨m₀', m₁'⟩, ⟨a', r₀', s₀', r₁', s₁'⟩, ⟨u', w', reply', ⟨⟩⟩⟩ h
  simp only [ddhOTSenderViewWords, DDHOTSenderViewWords.mk.injEq] at h
  obtain ⟨hm₀, hm₁, ha, hr₀, hs₀, hr₁, hs₁, hw₀, hw₁⟩ := h
  refine PartyView.ext ?_ ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Prod.ext (F.encode_injective d hm₀) (F.encode_injective d hm₁)
  · simp only [ZMod.val_injective _ |>.eq_iff] at ha hr₀ hs₀ hr₁ hs₁
    rw [ha, hr₀, hs₀, hr₁, hs₁]
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (F.encode_injective d hw₀) (F.encode_injective d hw₁)
  · exact Round.received_message_eq_of_ne (by decide) _ _

/-- The words determine a receiver's view. -/
theorem ddhOTReceiverViewWords_injective (d : F.Desc) :
    Function.Injective (F.ddhOTReceiverViewWords d) := by
  rintro ⟨σ, b, ⟨u, w, reply, ⟨⟩⟩⟩ ⟨σ', b', ⟨u', w', reply', ⟨⟩⟩⟩ h
  injection h with hσ hb hu he₀ hc₀ he₁ hc₁
  refine PartyView.ext hσ (ZMod.val_injective _ hb) (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl)))
  · exact Round.received_message_ext fun _ => F.encode_injective d hu
  · exact Round.received_message_eq_of_ne (by decide) _ _
  · exact Round.received_message_ext fun _ =>
      Prod.ext (Prod.ext (F.encode_injective d he₀) (F.encode_injective d hc₀))
        (Prod.ext (F.encode_injective d he₁) (F.encode_injective d hc₁))

/-- The encoding of `ddhOTFamily` for machines. Group parameters are written with `F.encDesc`.
The sender's input `(m₀, m₁)` is the pair of words `(F.encode d m₀, F.encode d m₁)`
(`encPair encBits encBits`) and the receiver's input is its choice bit (`encBool`). The sender's
output `()` is the empty word (`encUnit`) and the receiver's output `m_σ` is the word
`F.encode d m_σ`. The sender's and the receiver's views are their view words
(`ddhOTSenderViewWords`, `ddhOTReceiverViewWords`), encoded by `encDDHOTSenderViewWords` and
`encDDHOTReceiverViewWords`. -/
@[expose] noncomputable def ddhOTEncoding : F.ddhOTFamily.Encoding where
  desc := F.encDesc
  input :=
    { Rep := OTIn (List Bool)
      enc := fun i => Fin.cases (motive := fun i => OTIn (List Bool) i ↪ List Bool)
        (encPair encBits encBits) (fun _ => encBool) i
      rep := fun _ d i => Fin.cases (motive := fun i => OTIn (F.Carrier d) i ↪ OTIn (List Bool) i)
        ⟨Prod.map (F.encode d) (F.encode d), (F.encode_injective d).prodMap (F.encode_injective d)⟩
        (fun _ => Function.Embedding.refl Bool) i }
  output :=
    { Rep := OTOut (List Bool)
      enc := fun i => Fin.cases (motive := fun i => OTOut (List Bool) i ↪ List Bool) encUnit
        (fun _ => encBits) i
      rep := fun _ d i =>
        Fin.cases (motive := fun i => OTOut (F.Carrier d) i ↪ OTOut (List Bool) i)
          (Function.Embedding.refl Unit) (fun _ => ⟨F.encode d, F.encode_injective d⟩) i }
  view :=
    { Rep := DDHOTViewWords
      enc := fun i => Fin.cases (motive := fun i => DDHOTViewWords i ↪ List Bool)
        encDDHOTSenderViewWords (fun _ => encDDHOTReceiverViewWords) i
      rep := fun _ d i => Fin.cases (motive := fun i =>
          PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d)) (ddhOTSchedule (F.Carrier d)) i ↪
            DDHOTViewWords i)
        ⟨F.ddhOTSenderViewWords d, F.ddhOTSenderViewWords_injective d⟩
        (Fin.cases (motive := fun j => PartyView (OTIn (F.Carrier d)) (DDHOTCoins (F.order d))
            (ddhOTSchedule (F.Carrier d)) j.succ ↪ DDHOTViewWords j.succ)
          ⟨F.ddhOTReceiverViewWords d, F.ddhOTReceiverViewWords_injective d⟩
          fun k => k.elim0) i }

/-! ### Corrupted receiver: the reduction to DDH -/

/-- The DDH distinguisher built from an environment `Z` that corrupts the receiver: given the
security parameter `n`, group parameters `d` and a DDH triple `(u, v, w)`, run `Z.choose`, draw
the receiver's coin `b` and the chosen branch's coins `r, s` with `sampleExp`, and run
`ddhOTReductionWithCoins` with `Z.guess`, which embeds the triple into the unchosen branch. -/
@[expose] noncomputable def ddhOTReceiverToDDHDistinguisher (Z : Environment F.ddhOTFamily {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← Z.choose n d
  let b ← F.sampleExp n d
  let r ← F.sampleExp n d
  let s ← F.sampleExp n d
  ddhOTReductionWithCoins (F.generator d) c.inputs (Z.guess n d c.state)
    (b : ZMod (F.order d)) (r : ZMod (F.order d)) (s : ZMod (F.order d)) u v w

/-- The reduction with exact uniform coins: run `Z.choose`, then `ddhOTReduction`. It is not PPT;
it compares the games with the DDH games of `ddhOTReceiverToDDHDistinguisher`. -/
private noncomputable def ddhOTReceiverToDDHExact (Z : Environment F.ddhOTFamily {1}) :
    F.DDHDistinguisher := fun n d u v w => do
  let c ← Z.choose n d
  ddhOTReduction (F.generator d) (F.order d) c.inputs (Z.guess n d c.state) u v w

/-- The real game against a corrupted receiver is the real DDH game of the exact reduction. -/
private theorem realGame_receiver_eq (setup : ℕ → PMF F.Desc) (Z : Environment F.ddhOTFamily {1})
    (n : ℕ) :
    F.ddhOTFamily.realGame setup {1} Z n =
      F.ddhRealGame setup (F.ddhOTReceiverToDDHExact Z) n := by
  simp only [ProtocolFamily.realGame, ddhRealGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  simp only [real_receiver_eq_ddhRealExperiment, eval_ddhRealExperiment,
    ddhOTReceiverToDDHExact, ProbComp.eval_bind]
  pmf_swap

/-- The ideal game against a corrupted receiver with the exact-sampling simulator is the random
DDH game of the exact reduction. -/
private theorem idealGame_receiver_eq (setup : ℕ → PMF F.Desc) (Z : Environment F.ddhOTFamily {1})
    (n : ℕ) :
    F.ddhOTFamily.idealGame setup {1}
        (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n =
      F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact Z) n := by
  simp only [ProtocolFamily.idealGame, ddhRandomGame, Game.withSetup, PMF.monad_bind_eq_bind]
  refine congrArg (PMF.bind _) (funext fun d => ?_)
  simp only [← ProbComp.eval_bind,
    ideal_receiver_eq_ddhRandomExperiment _ _ (F.smul_generator_surjective d)]
  simp only [eval_ddhRandomExperiment, ddhOTReceiverToDDHExact, ProbComp.eval_bind]
  pmf_swap

/-- On every triple, the exact and the `sampleExp` reductions accept with probabilities within
`3 / 2 ^ n`. -/
private theorem advantage_ddhOTReceiverToDDHExact_le (Z : Environment F.ddhOTFamily {1}) (n : ℕ)
    (d : F.Desc) (u v w : F.Carrier d) :
    Game.advantage (ProbComp.eval (F.ddhOTReceiverToDDHExact Z n d u v w))
      (ProbComp.eval (F.ddhOTReceiverToDDHDistinguisher Z n d u v w)) ≤ 3 / 2 ^ n := by
  simp only [ddhOTReceiverToDDHExact, ddhOTReceiverToDDHDistinguisher, ddhOTReduction,
    ProbComp.eval_bind, ProbComp.eval_uniform]
  refine Game.advantage_bind_le_nnreal _ _ _ fun c => ?_
  rw [Game.advantage_comm]
  exact F.advantage_bind_sampleExp_triple_le n d fun b r s =>
    ProbComp.eval (ddhOTReductionWithCoins (F.generator d) c.inputs (Z.guess n d c.state)
      b r s u v w)

/-- **Concrete bound for a corrupted receiver**: the advantage of `Z` between the real game and
the ideal game with the exact-sampling simulator `ddhOTReceiverSim` is at most the DDH advantage
of `ddhOTReceiverToDDHDistinguisher Z` plus `6 / 2 ^ n`. -/
theorem advantage_ddhOTReceiverGame_le (setup : ℕ → PMF F.Desc)
    (Z : Environment F.ddhOTFamily {1}) (n : ℕ) :
    Game.advantage (F.ddhOTFamily.realGame setup {1} Z n)
        (F.ddhOTFamily.idealGame setup {1}
          (fun _ d => ddhOTReceiverSim (F.generator d) (F.order d)) Z n) ≤
      Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
        (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 6 / 2 ^ n := by
  rw [realGame_receiver_eq, idealGame_receiver_eq]
  have hreal : Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHExact Z) n)
      (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) ≤ 3 / 2 ^ n := by
    simp only [ddhRealGame, Game.withSetup, eval_ddhRealExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        F.advantage_ddhOTReceiverToDDHExact_le Z n d _ _ _
  have hrandom : Game.advantage (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
      (F.ddhRandomGame setup (F.ddhOTReceiverToDDHExact Z) n) ≤ 3 / 2 ^ n := by
    rw [Game.advantage_comm]
    simp only [ddhRandomGame, Game.withSetup, eval_ddhRandomExperiment]
    exact Game.advantage_bind_le_nnreal _ _ _ fun d =>
      Game.advantage_bind_le_nnreal _ _ _ fun a => Game.advantage_bind_le_nnreal _ _ _ fun b =>
        Game.advantage_bind_le_nnreal _ _ _ fun c =>
          F.advantage_ddhOTReceiverToDDHExact_le Z n d _ _ _
  calc _ ≤ 3 / 2 ^ n + (Game.advantage (F.ddhRealGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n)
          (F.ddhRandomGame setup (F.ddhOTReceiverToDDHDistinguisher Z) n) + 3 / 2 ^ n) :=
        (Game.advantage_triangle _ _ _).trans (add_le_add hreal
          ((Game.advantage_triangle _ _ _).trans (add_le_add le_rfl hrandom)))
    _ = _ := by ring

/-! ### Corrupted receiver: efficiency of the reduction -/

/-- The view words that `ddhOTReceiverToDDHDistinguisher` gives the environment, from the DDH
input `x`, the words `m₀, m₁` of the messages, the choice bit `σ` and the coins `b, r, s`. The
second components of the branch ciphertexts add the encoded messages with `F.add`, and `-b` is
`F.order d - b % F.order d`. -/
private def ddhOTReceiverViewWordsOf (x : F.DDHInput) (m₀ m₁ : List Bool) (σ : Bool)
    (b r s : ℕ) : DDHOTReceiverViewWords :=
  let d := x.groupParameters
  let q := F.order d
  let e := (r : ZMod q) • F.generator d + (s : ZMod q) • x.leftPublic
  let chosen := F.encode d ((b : ZMod q) • e)
  let other := F.encode d (x.candidateShared + ((q - b % q : ℕ) : ZMod q) • x.rightPublic)
  ⟨σ, b % q, F.encode d x.leftPublic, if σ then F.encode d x.rightPublic else F.encode d e,
    F.add (d, if σ then other else chosen, m₀),
    if σ then F.encode d e else F.encode d x.rightPublic,
    F.add (d, if σ then chosen else other, m₁)⟩

/-- The word of the outputs that `ddhOTReceiverToDDHDistinguisher` gives the environment, from the
words `m₀, m₁` of the messages and the choice bit `σ`: the table of the empty word for the sender
and the word of `m_σ` for the receiver. -/
private noncomputable def ddhOTOutputWords (m₀ m₁ : List Bool) (σ : Bool) : List Bool :=
  encPi encBits fun i : Fin 2 =>
    Fin.cases (motive := fun _ => List Bool) [] (fun _ => if σ then m₁ else m₀) i

/-- The words of the guessing-stage input that `ddhOTReceiverToDDHDistinguisher` gives the
environment, laid out as `encGuessInputFields`: the security parameter, the group parameters, the
state, the table of the receiver's view words, and the word of the outputs. -/
private noncomputable def ddhOTReceiverGuessWords (x : F.DDHInput) (m₀ m₁ : List Bool) (σ : Bool)
    (state : List Bool) (b r s : ℕ) : ℕ × F.Desc × List Bool × List Bool × List Bool :=
  (x.secParam, x.groupParameters, state,
    encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
      encDDHOTReceiverViewWords (F.ddhOTReceiverViewWordsOf x m₀ m₁ σ b r s),
    ddhOTOutputWords m₀ m₁ σ)

/-- The words that an environment's choosing stage writes for `ddhOTEncoding`: the table of the
parties' input words and the state. -/
private abbrev ChoiceWords : Type := ((i : Fin 2) → F.ddhOTEncoding.input.Rep i) × List Bool

/-- What the last stage of `ddhOTReceiverToDDHDistinguisher` reads: the DDH input, the words of
the environment's choice and the three coins. -/
private abbrev ReceiverReductionWords : Type := (((F.DDHInput × F.ChoiceWords) × ℕ) × ℕ) × ℕ

/-- `ddhOTReceiverToDDHDistinguisher Z` is uniform strict PPT whenever `Z` is. -/
theorem isPPT_ddhOTReceiverToDDHDistinguisher {Z : Environment F.ddhOTFamily {1}}
    (hZ : Z.IsPPT F.ddhOTEncoding) : (F.ddhOTReceiverToDDHDistinguisher Z).IsPPT := by
  obtain ⟨W, hW, hWeq⟩ := hZ.guess.exists_bool_factor (encGuessInput_apply F.ddhOTEncoding)
  let E := encPair (encPair (encPair (encPair F.encDDHInput
    (encPair (encDPi F.ddhOTEncoding.input.enc) encBits)) encNat) encNat) encNat
  have hx : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.1.1.1) E
      F.encDDHInput := by fun_prop
  have hcw : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.1.1.2) E
      (encPair (encDPi F.ddhOTEncoding.input.enc) encBits) := by fun_prop
  have hb : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.1.2) E
      encNat := by fun_prop
  have hr : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.2) E
      encNat := by fun_prop
  have hs : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.2) E
      encNat := by fun_prop
  have htable := hcw.fst'
  have hstate := hcw.snd'
  have hin₀ : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.1.1.2.1 0) E
      (encPair encBits encBits) :=
    (ComputableInPolyTime.dpi_apply F.ddhOTEncoding.input.enc 0).comp htable
  have hσ : ComputableInPolyTime (fun p : F.ReceiverReductionWords => p.1.1.1.2.1 1) E
      encBool :=
    (ComputableInPolyTime.dpi_apply F.ddhOTEncoding.input.enc 1).comp htable
  have hm₀ := hin₀.fst'
  have hm₁ := hin₀.snd'
  have hd := F.encDDHInput_groupParameters_polyTime hx
  have hu := F.encDDHInput_leftPublic_polyTime hx
  have hv := F.encDDHInput_rightPublic_polyTime hx
  have hw := F.encDDHInput_candidateShared_polyTime hx
  have hq := F.computableInPolyTime_order.comp hd
  have hmod := ComputableInPolyTime.binary_mod' hb hq
  have he := computableInPolyTime_encode_add hd
    (computableInPolyTime_encode_natCast_smul hd hr (computableInPolyTime_encode_generator hd))
    (computableInPolyTime_encode_natCast_smul hd hs hu)
  have hchosen := computableInPolyTime_encode_natCast_smul hd hb he
  have hother := computableInPolyTime_encode_add hd hw
    (computableInPolyTime_encode_natCast_smul hd (ComputableInPolyTime.binary_sub' hq hmod) hv)
  have hview : ComputableInPolyTime (fun p : F.ReceiverReductionWords =>
      F.ddhOTReceiverViewWordsOf p.1.1.1.1 (p.1.1.1.2.1 0).1 (p.1.1.1.2.1 0).2 (p.1.1.1.2.1 1)
        p.1.1.2 p.1.2 p.2) E encDDHOTReceiverViewWords :=
    encDDHOTReceiverViewWords_mk_polyTime hσ hmod hu (hσ.ite' hv he)
      (F.computableInPolyTime_add.comp (hd.prod ((hσ.ite' hother hchosen).prod hm₀)))
      (hσ.ite' he hv)
      (F.computableInPolyTime_add.comp (hd.prod ((hσ.ite' hchosen hother).prod hm₁)))
  have hviews : ComputableInPolyTime (fun p : F.ReceiverReductionWords =>
      encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
        encDDHOTReceiverViewWords (F.ddhOTReceiverViewWordsOf p.1.1.1.1 (p.1.1.1.2.1 0).1
          (p.1.1.1.2.1 0).2 (p.1.1.1.2.1 1) p.1.1.2 p.1.2 p.2)) E encBits :=
    (ComputableInPolyTime.pi fun _ => hview.encoding_comp).encoding_comp
  have houtputs : ComputableInPolyTime (fun p : F.ReceiverReductionWords =>
      ddhOTOutputWords (p.1.1.1.2.1 0).1 (p.1.1.1.2.1 0).2 (p.1.1.1.2.1 1)) E encBits := by
    unfold ddhOTOutputWords
    refine (ComputableInPolyTime.pi fun i => ?_).encoding_comp
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ComputableInPolyTime.const []
    · exact hσ.ite' hm₁ hm₀
  have hwords : ComputableInPolyTime (fun p : F.ReceiverReductionWords =>
      F.ddhOTReceiverGuessWords p.1.1.1.1 (p.1.1.1.2.1 0).1 (p.1.1.1.2.1 0).2 (p.1.1.1.2.1 1)
        p.1.1.1.2.2 p.1.1.2 p.1.2 p.2) E (encGuessInputFields F.ddhOTEncoding) :=
    (F.encDDHInput_secParam_polyTime hx).prod (hd.prod (hstate.prod (hviews.prod houtputs)))
  have hsample {α : Type} {enc : α ↪ List Bool} {x : α → F.DDHInput}
      (hx : ComputableInPolyTime x enc F.encDDHInput) :
      IsPPTOn enc encNat fun a => F.sampleExp (x a).secParam (x a).groupParameters :=
    F.isPPTOn_sampleExp (by fun_prop) (by fun_prop)
  have hprogram : IsPPTOn F.encDDHInput encBool (fun x => do
      let cw ← (fun c => ((fun i => F.ddhOTEncoding.input.rep x.secParam x.groupParameters i
          (c.inputs i)), c.state)) <$> Z.choose x.secParam x.groupParameters
      let b ← F.sampleExp x.secParam x.groupParameters
      let r ← F.sampleExp x.secParam x.groupParameters
      let s ← F.sampleExp x.secParam x.groupParameters
      W (F.ddhOTReceiverGuessWords x (cw.1 0).1 (cw.1 0).2 (cw.1 1) cw.2 b r s)) := by
    refine IsPPTOn.bind_with (hZ.choose.preprocess
      (prepare := fun x : F.DDHInput => (x.secParam, x.groupParameters)) (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    refine IsPPTOn.bind_with (hsample (by fun_prop)) ?_
    exact hW.preprocess hwords
  refine hprogram.congr fun x => ?_
  simp only [ddhOTReceiverToDDHDistinguisher, ProbComp.eval_bind, ProbComp.eval_map, PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun c => congrArg (PMF.bind _) (funext fun b =>
    congrArg (PMF.bind _) (funext fun r => congrArg (PMF.bind _) (funext fun s => ?_))))
  have hneg : ((F.order x.groupParameters - b % F.order x.groupParameters : ℕ) :
      ZMod (F.order x.groupParameters)) = -(b : ZMod (F.order x.groupParameters)) := by
    rw [Nat.cast_sub (Nat.le_of_lt (Nat.mod_lt _ (F.prime_order _).pos)), ZMod.natCast_self,
      ZMod.natCast_mod, zero_sub]
  obtain ⟨xs, state⟩ := c
  obtain ⟨⟨m₀, m₁⟩, σ, rfl⟩ : ∃ (m : F.Carrier x.groupParameters × F.Carrier x.groupParameters)
      (σ : Bool), xs = fun i =>
        Fin.cases (motive := fun i => OTIn (F.Carrier x.groupParameters) i) m (fun _ => σ) i :=
    ⟨xs 0, xs 1, funext fun i => Fin.cases rfl (fun j => Fin.cases rfl (fun k => k.elim0) j) i⟩
  refine congrArg ProbComp.eval (Eq.trans (congrArg W ?_)
    (hWeq ⟨x.secParam, x.groupParameters, state, _, _⟩).symm)
  refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ ?_)))
  · refine Eq.trans ?_
      (F.ddhOTEncoding.view.encCoalition_singleton x.secParam x.groupParameters 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encDDHOTReceiverViewWords ?_)
    let q := F.order x.groupParameters
    let e := (r : ZMod q) • F.generator x.groupParameters + (s : ZMod q) • x.leftPublic
    cases σ
    · change F.ddhOTReceiverViewWordsOf x (F.encode _ m₀) (F.encode _ m₁) false b r s =
        F.ddhOTReceiverViewWords x.groupParameters (ddhOTReceiverView false (b : ZMod q)
          x.leftPublic ((e, (b : ZMod q) • e + m₀),
            (x.rightPublic, x.candidateShared - (b : ZMod q) • x.rightPublic + m₁)))
      simp only [ddhOTReceiverViewWordsOf, ddhOTReceiverViewWords, ddhOTReceiverView,
        Bool.false_eq_true, ↓reduceIte, F.add_encode, hneg, neg_smul, ← sub_eq_add_neg,
        ZMod.val_natCast]
      rfl
    · change F.ddhOTReceiverViewWordsOf x (F.encode _ m₀) (F.encode _ m₁) true b r s =
        F.ddhOTReceiverViewWords x.groupParameters (ddhOTReceiverView true (b : ZMod q)
          x.leftPublic ((x.rightPublic, x.candidateShared - (b : ZMod q) • x.rightPublic + m₀),
            (e, (b : ZMod q) • e + m₁)))
      simp only [ddhOTReceiverViewWordsOf, ddhOTReceiverViewWords, ddhOTReceiverView, ↓reduceIte,
        F.add_encode, hneg, neg_smul, ← sub_eq_add_neg, ZMod.val_natCast]
      rfl
  · simp only [ddhOTReceiverGuessWords, ddhOTOutputWords, PartyEncoding.encAll,
      Function.Embedding.coeFn_mk, encDPi_apply]
    congr 1
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    cases σ <;> rfl

end Cslib.Crypto.PrimeOrderGroupFamily
