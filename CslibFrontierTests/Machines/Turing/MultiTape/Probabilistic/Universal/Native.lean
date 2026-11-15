/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of candidate modules)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Native

/-! Checked boundary clients for retained first-order initialization and table lookup. -/

public section

namespace CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.Native

open Turing.MultiTapeTM Turing.MultiTapeTM.Internal
open Turing.MultiTapePTM.Universal

/-- Channel reads cover negative, in-range and right-blank answer positions. -/
example :
    Channel.read ⟨[], [4], -1⟩ = none ∧
      Channel.read ⟨[], [4], 0⟩ = some 4 ∧
      Channel.read ⟨[], [4], 1⟩ = none := by
  decide

/-- Reply installation updates one in-range channel and leaves a malformed short list unchanged. -/
example :
    let cfg : ICfg := ⟨some (some 0), 1, [], [], [⟨[7], [], 0⟩]⟩
    let inRange : Fin 2 := ⟨0, by decide⟩
    let outOfRange : Fin 2 := ⟨1, by decide⟩
    ((cfg.receive inRange 1 [3]).channels.getD 0 .blank).query = [] ∧
      ((cfg.receive inRange 1 [3]).channels.getD 0 .blank).answer = [3] ∧
      ((cfg.receive inRange 1 [3]).channels.getD 0 .blank).answerPos = 0 ∧
      ((cfg.receive outOfRange 1 [3]).channels.getD 0 .blank).query = [7] ∧
      (ICfg.receiveCompiler 2).outputBits (cfg, inRange, 1, [3]) =
        (eICfg (cfg.receive inRange 1 [3])).length := by
  decide

/-- Valid and invalid initial tags preserve the exact trap convention and declared list lengths. -/
example :
    let valid : Desc := ⟨2, 3, 1, 1, []⟩
    let invalid : Desc := ⟨2, 3, 1, 3, []⟩
    (ICfg.init valid).control = some (some 1) ∧
      (ICfg.init invalid).control = some none ∧
      (ICfg.init valid).workTapes.length = 2 ∧
      (ICfg.init valid).channels.length = 1 := by
  decide

/-- The combined retained initializer covers the all-zero descriptor boundary. -/
example :
    let zero : Desc := ⟨0, 0, 0, 0, []⟩
    (ICfg.init zero).control = some none ∧
      (ICfg.init zero).workTapes.length = 0 ∧
      (ICfg.init zero).channels.length = 0 ∧
      ICfg.initCompiler.outputBits zero = (eICfg (ICfg.init zero)).length := by
  decide

/-- Initialization exposes exact encoded output size, including every replicated frame. -/
example (d : Desc) : ICfg.initCompiler.outputBits d = (eICfg (ICfg.init d)).length :=
  rfl

/-- Local execution defaults short action lists and ignores actions past stored tape and channel
lists. -/
example :
    let tape := Turing.MultiTapeTM.Universal.Tape.blank
    let channel := Channel.blank
    let cfg : ICfg := ⟨some (some 0), 1, [tape], [], [channel]⟩
    let shortOrdinary : Turing.MultiTapeTM.Universal.Act := ⟨0, [], none, some 0⟩
    let extraOrdinary : Turing.MultiTapeTM.Universal.Act :=
      ⟨0, [(some (some 1), 0), (some (some 2), 0)], none, some 0⟩
    (cfg.step [] 1 shortOrdinary [] []).workTapes.length = 1 ∧
      ((cfg.step [] 1 shortOrdinary [] []).workTapes.getD 0 .blank).head = 0 ∧
      (cfg.step [] 1 shortOrdinary [] []).channels.length = 1 ∧
      ((cfg.step [] 1 shortOrdinary [] []).channels.getD 0 .blank).query = [] ∧
      (cfg.step [] 1 extraOrdinary [some 3, some 4] [0, .pos]).workTapes.length = 1 ∧
      (cfg.step [] 1 extraOrdinary [some 3, some 4] [0, .pos]).channels.length = 1 := by
  decide

/-- Halted, trap, missing-table and all-zero descriptions take their exact local branches. -/
example :
    let halted : ICfg := ⟨none, 1, [], [], []⟩
    let trap : ICfg := ⟨some none, 1, [], [], []⟩
    let active : ICfg := ⟨some (some 0), 1, [], [], []⟩
    let d : Desc := ⟨0, 1, 0, 0, []⟩
    let zero : Desc := ⟨0, 0, 0, 0, []⟩
    (match halted.commandAt 0 d [] false with
      | .local next => next.control = none ∧ next.inputPos = 1
      | .query .. => False) ∧
    (match trap.commandAt 0 d [] false with
      | .local next => next.control = none
      | .query .. => False) ∧
    (match active.commandAt 0 d [] false with
      | .local next => next.control = none
      | .query .. => False) ∧
    (match (ICfg.init zero).commandAt 0 zero [] false with
      | .local next => next.control = none
      | .query .. => False) := by
  simp [ICfg.commandAt, ICfg.init, ICfg.halt]

/-- Query validation rejects invalid tags and preserves the exact request on a valid branch. -/
example :
    let cfg : ICfg := ⟨some (some 0), 1, [], [], [⟨[7], [], 0⟩]⟩
    let d : Desc := ⟨0, 2, 1, 0, []⟩
    (match cfg.command 1 d [] (.query 1 1) with
      | .local next => next.control = none
      | .query .. => False) ∧
    (match cfg.command 1 d [] (.query 0 2) with
      | .local next => next.control = none
      | .query .. => False) ∧
    (match cfg.command 1 d [] (.query 0 1) with
      | .query operation request next _ =>
          operation.val = 0 ∧ request = [7] ∧ next = 1
      | .local _ => False) := by
  norm_num [ICfg.command, ICfg.halt]

/-- Table lookup, coin selection and query construction preserve the buffered request exactly. -/
example :
    let cfg : ICfg := ⟨some (some 0), 1, [], [], [⟨[7], [], 0⟩]⟩
    let action : Act := .query 0 1
    let branches : Branches := ⟨action, .query 0 0⟩
    let key := cfg.key [] 0
    let d : Desc := ⟨0, 2, 1, 0, [(key, branches)]⟩
    (match cfg.commandAt 1 d [] false with
      | .query operation request next _ =>
          operation.val = 0 ∧ request = [7] ∧ next = 1
      | .local _ => False) ∧
      (ICfg.commandAtCompiler 1).outputBits (d, [], cfg, false) =
        (eCommand 1 (cfg.commandAt 1 d [] false)).length := by
  norm_num [ICfg.commandAt, ICfg.command, ICfg.key]
  rfl

end CslibFrontierTests.Machines.Turing.MultiTape.Probabilistic.Universal.Native
