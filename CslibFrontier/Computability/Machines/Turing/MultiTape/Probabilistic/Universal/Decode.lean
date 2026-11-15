/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.FirstOrder
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Decode

/-!
# Constructive decoders for first-order probabilistic universal data

The injective encodings of probabilistic transition keys, actions, branches and descriptions, and
of the first-order channel and configuration storage, all have explicit total decoders. These
decoders are proof-only certificates: a retained native interpreter must still execute and charge
its concrete parsing machines.

## Main definitions

* `Turing.MultiTapePTM.Universal.keyDecoder`, `.actDecoder`, `.branchesDecoder`, `.descDecoder`:
  constructive decoders for probabilistic descriptions and their components.
* `Turing.MultiTapePTM.Universal.channelDecoder`, `.iCfgDecoder`: constructive decoders for the
  first-order interpreter storage.

## Main results

Every decoder's `Decoder.decode_enc` field proves that it retracts the corresponding encoding.
-/

public section

namespace Turing.MultiTapePTM.Universal

open Turing.MultiTapeTM

private abbrev symDecoder := Turing.MultiTapeTM.Universal.symDecoder
private abbrev signDecoder := Turing.MultiTapeTM.Universal.signDecoder
private abbrev ordinaryActDecoder := Turing.MultiTapeTM.Universal.actDecoder
private abbrev tapeDecoder := Turing.MultiTapeTM.Universal.tapeDecoder

/-- Probabilistic transition keys, including the answer-symbol vector. -/
def keyDecoder : Decoder eKey :=
  (Decoder.pair .unary
    (.pair symDecoder (.pair (.list symDecoder) (.list symDecoder)))).map
    (fun (state, input, work, answers) => ⟨⟨state, input, work⟩, answers⟩)
    (fun k => (k.state, k.input, k.work, k.answers)) (fun _ => rfl) fun _ => rfl

/-- Tagged ordinary and query actions. -/
def actDecoder : Decoder eAct :=
  (Decoder.sum
    (Decoder.pair ordinaryActDecoder (.pair (.list symDecoder) (.list signDecoder)))
    (Decoder.pair .unary .unary)).map
    (fun action => match action with
      | .inl (ordinary, querySymbols, answerMoves) =>
          .step ordinary querySymbols answerMoves
      | .inr (operation, next) => .query operation next)
    eAct_toSum (fun action => by cases action <;> rfl) fun action => by
      rcases action with ⟨ordinary, querySymbols, answerMoves⟩ | ⟨operation, next⟩ <;> rfl

/-- Both explicitly stored Boolean action branches. -/
def branchesDecoder : Decoder eBranches :=
  (Decoder.pair actDecoder actDecoder).map
    (fun branches => ⟨branches.1, branches.2⟩)
    (fun branches => (branches.falseBranch, branches.trueBranch)) (fun _ => rfl) fun _ => rfl

/-- Complete probabilistic descriptions. -/
def descDecoder : Decoder eDesc :=
  (Decoder.pair .unary
    (.pair .unary
      (.pair .unary
        (.pair .unary (.list (.pair keyDecoder branchesDecoder)))))).map
    (fun (tapes, states, operations, q₀, table) => ⟨tapes, states, operations, q₀, table⟩)
    (fun d => (d.tapes, d.states, d.operations, d.q₀, d.table)) (fun _ => rfl) fun _ => rfl

/-- One first-order oracle channel. -/
def channelDecoder : Decoder eChannel :=
  (Decoder.pair (.list .unary)
    (.pair (.list .unary) Turing.MultiTapeTM.Universal.intUnaryDecoder)).map
    (fun (query, answer, answerPos) => ⟨query, answer, answerPos⟩)
    (fun channel => (channel.query, channel.answer, channel.answerPos))
    (fun _ => rfl) fun _ => rfl

/-- Complete first-order interpreter storage. -/
def iCfgDecoder : Decoder eICfg :=
  (Decoder.pair (.option (.option .unary))
    (.pair .nat
      (.pair (.list tapeDecoder)
        (.pair (.list .unary) (.list channelDecoder))))).map
    (fun (control, inputPos, workTapes, output, channels) =>
      ⟨control, inputPos, workTapes, output, channels⟩)
    (fun cfg => (cfg.control, cfg.inputPos, cfg.workTapes, cfg.output, cfg.channels))
    (fun _ => rfl) fun _ => rfl

end Turing.MultiTapePTM.Universal
