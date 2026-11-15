/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import
  CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Universal.Description
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Complexity
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Correct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bound
import Mathlib.Data.List.GetD

/-!
# First-order storage for universal oracle-machine steps

This deterministic source layer is shared by the fixed-channel oracle interpreter and its retained
native implementation. It represents an oracle-machine configuration with ordinary lists and
natural-number tags, validates dynamic operation and successor tags before constructing a typed
command, and relates that storage exactly to `Desc.toMachine`.

It does not execute an oracle call, dispatch a physical `Fin r` channel, truncate or decode a
reply, iterate a clock, or claim that these source definitions run in constant time. A native
consumer must retain and charge the machines that decode, scan, validate, update, and encode this
data.

## Main definitions

* `Turing.MultiTapePTM.Universal.Channel`, `.ICfg`: first-order channel and machine storage.
* `Turing.MultiTapePTM.Universal.Command`: a locally completed step or validated external query.
* `Turing.MultiTapePTM.Universal.ICfg.commandAt`: first-match table lookup and action validation.

## Main results

* `Turing.MultiTapePTM.Universal.ICfg.toConfig_init`: exact initial-storage bridge.
* `Turing.MultiTapePTM.Universal.ICfg.toConfig_step`, `.toConfig_halt`, `.toConfig_receive`:
  exact one-step bridges to native configurations.
* `Turing.MultiTapePTM.Universal.ICfg.key_toConfig`: first-order and native lookup keys agree.
-/

@[expose] public section

namespace Turing.MultiTapePTM.Universal

open Turing.MultiTapeMachine Turing.MultiTapeTM Turing.MultiTapeTM.Universal

/-- Finite storage for one described oracle channel. -/
structure Channel where
  /-- Pending request buffer. -/
  query : List ℕ
  /-- Installed reply word. -/
  answer : List ℕ
  /-- Current answer-head position. Negative positions read blank. -/
  answerPos : ℤ
deriving Inhabited

/-- Encoding of a pending request, installed answer and answer-head position. -/
enc_structure eChannel : Channel where
  query : (encList encUnary), answer : (encList encUnary), answerPos : encIntUnary

/-- First-order storage of the interpreted machine. -/
structure ICfg where
  /-- `none` means halted; `some none` is the trap; `some (some q)` is user state `q`. -/
  control : Option (Option ℕ)
  /-- Input-head position in the deterministic universal convention. -/
  inputPos : ℕ
  /-- Work-tape zippers. -/
  workTapes : List Turing.MultiTapeTM.Universal.Tape
  /-- Accumulated output word. -/
  output : List ℕ
  /-- Channel storage, in operation-tag order. -/
  channels : List Channel
deriving Inhabited

/-- Encoding of the full first-order interpreter configuration. -/
enc_structure eICfg : ICfg where
  control : (encOption (encOption encUnary)), inputPos : encNat,
  workTapes : (encList eTape), output : (encList encUnary), channels : (encList eChannel)

/-- Blank zipper used by every work tape initially. -/
def blankTape : Turing.MultiTapeTM.Universal.Tape := ⟨0, [], []⟩

/-- Blank channel storage. -/
def Channel.blank : Channel := ⟨[], [], 0⟩

/-- Read the source symbol under an answer head. -/
def Channel.read (channel : Channel) : Option ℕ :=
  if 0 ≤ channel.answerPos then channel.answer[channel.answerPos.toNat]? else none

/-- Apply one source local step to a channel. -/
def Channel.step (channel : Channel) (symbol : Option ℕ) (move : SignType) : Channel :=
  ⟨channel.query ++ symbol.toList, channel.answer, channel.answerPos + move⟩

/-- Install a reply at answer position zero and clear the submitted request. -/
def Channel.receive (answer : List ℕ) : Channel := ⟨[], answer, 0⟩

/-- Initialize first-order interpreter storage. Invalid initial tags enter the explicit trap
control and take one source instruction to halt, exactly as `Desc.toMachine`. -/
def ICfg.init (d : Desc) : ICfg where
  control := some ((Fin.ofNat? d.states d.q₀).map Fin.val)
  inputPos := 1
  workTapes := List.replicate d.tapes blankTape
  output := []
  channels := List.replicate d.operations .blank

/-- Shape and range invariant of first-order interpreter storage. -/
structure ICfg.Valid (d : Desc) (input : List ℕ) (cfg : ICfg) : Prop where
  /-- Every stored user-state tag is in range. -/
  control : ∀ state, cfg.control = some (some state) → state < d.states
  /-- The input head remains on the two boundary cells or the input word. -/
  inputPos : cfg.inputPos ≤ input.length + 1
  /-- There is exactly one work zipper per declared work tape. -/
  workTapes : cfg.workTapes.length = d.tapes
  /-- There is exactly one channel record per declared operation. -/
  channels : cfg.channels.length = d.operations

/-- Decode first-order control storage to the native denotation's nested finite control. -/
def decodeControl (states : ℕ) : Option (Option ℕ) → Option (Option (Fin states))
  | none => none
  | some none => some none
  | some (some state) => (Fin.ofNat? states state).map some

@[simp] theorem decodeControl_initial (states initial : ℕ) :
    decodeControl states (some ((Fin.ofNat? states initial).map Fin.val)) =
      some (Fin.ofNat? states initial) := by
  by_cases h : initial < states
  · simp only [Fin.ofNat?_eq_some_of_lt states initial h, Option.map_some, decodeControl]
  · simp only [Fin.ofNat?_eq_none_of_not_lt states initial h, Option.map_none, decodeControl]

/-- Read first-order storage as a native configuration of `Desc.toMachine`. The total definition
uses blanks for missing tapes/channels and clamps an invalid input position; `ICfg.Valid` proves
that neither fallback is used by an interpreter run. -/
def ICfg.toConfig (d : Desc) (input : List ℕ) (cfg : ICfg) :
    Config d.tapes ℕ (Option (Fin d.states)) (Fin d.operations) input where
  tapes :=
    { state := decodeControl d.states cfg.control
      inputPos := ⟨min cfg.inputPos (input.length + 1), by omega⟩
      workTapes := fun tape => (cfg.workTapes.getD tape.val blankTape).cellAt
      workTapePos := fun tape => (cfg.workTapes.getD tape.val blankTape).head
      output := cfg.output }
  channels := fun operation =>
    let channel := cfg.channels.getD operation.val .blank
    { queryBuffer := channel.query
      answer := channel.answer
      answerPos := channel.answerPos }

@[simp] theorem ICfg.toConfig_state (d : Desc) (input : List ℕ) (cfg : ICfg) :
    (cfg.toConfig d input).tapes.state = decodeControl d.states cfg.control :=
  rfl

/-- Initial first-order storage is well shaped. -/
theorem ICfg.valid_init (d : Desc) (input : List ℕ) : (ICfg.init d).Valid d input := by
  refine ⟨?_, by simp [ICfg.init], by simp [ICfg.init], by simp [ICfg.init]⟩
  intro state hstate
  simp only [ICfg.init, Option.some.injEq] at hstate
  obtain ⟨initial, hinitial, rfl⟩ := Option.map_eq_some_iff.mp hstate
  exact initial.isLt

/-- Initial first-order storage denotes the native initial configuration exactly. -/
theorem ICfg.toConfig_init (d : Desc) (input : List ℕ) :
    (ICfg.init d).toConfig d input = d.toMachine.initialConfig input := by
  ext <;> simp [ICfg.toConfig, ICfg.init, blankTape, Channel.blank,
    Turing.MultiTapeTM.Universal.Tape.cellAt, MultiTapePTM.Universal.Desc.toMachine,
    MultiTapeMachine.initialConfig]

/-- Current source input symbol. -/
def ICfg.inputSymbol (cfg : ICfg) (input : List ℕ) : Option ℕ :=
  Turing.MultiTapeTM.Universal.inputSymbol input cfg.inputPos

/-- Current source work-head symbols. -/
def ICfg.workSymbols (cfg : ICfg) : List (Option ℕ) :=
  cfg.workTapes.map Turing.MultiTapeTM.Universal.Tape.read

/-- Current source answer-head symbols. -/
def ICfg.answerSymbols (cfg : ICfg) : List (Option ℕ) := cfg.channels.map Channel.read

/-- A first-order key read from interpreter storage. -/
def ICfg.key (cfg : ICfg) (input : List ℕ) (state : ℕ) : Key :=
  { state := state
    input := cfg.inputSymbol input
    work := cfg.workSymbols
    answers := cfg.answerSymbols }

/-- Decode an ordinary successor tag to the first-order native control convention. -/
def nextIControl (states : ℕ) : Option ℕ → Option (Option ℕ)
  | none => none
  | some next => if next < states then some (some next) else none

/-- Apply an ordinary local action and its per-channel writes and answer-head moves. -/
def ICfg.step (cfg : ICfg) (input : List ℕ) (states : ℕ)
    (ordinary : Turing.MultiTapeTM.Universal.Act) (querySymbols : List (Option ℕ))
    (answerMoves : List SignType) : ICfg where
  control := nextIControl states ordinary.state
  inputPos := moveInput cfg.inputPos (cfg.inputSymbol input) ordinary.inputTape
  workTapes := applyTapes cfg.workTapes ordinary.workTapes
  output := cfg.output ++ ordinary.output.toList
  channels := cfg.channels.mapIdx fun operation channel =>
    channel.step (querySymbols.getD operation none) (answerMoves.getD operation 0)

/-- Halt locally without changing any tape, output or channel contents. -/
def ICfg.halt (cfg : ICfg) : ICfg := { cfg with control := none }

/-- Install a source reply on one checked finite channel. -/
def ICfg.receive {r : ℕ} (cfg : ICfg) (operation : Fin r) (next : ℕ)
    (reply : List ℕ) : ICfg where
  control := some (some next)
  inputPos := cfg.inputPos
  workTapes := cfg.workTapes
  output := cfg.output
  channels := cfg.channels.modify operation.val fun _ => Channel.receive reply

@[simp] theorem decodeControl_nextIControl (states : ℕ) (next : Option ℕ) :
    decodeControl states (nextIControl states next) = nextControl states next := by
  cases next with
  | none => rfl
  | some next =>
    by_cases h : next < states
    · simp only [nextIControl, h, ↓reduceIte, decodeControl,
        Fin.ofNat?_eq_some_of_lt states next h, Option.map_some, nextControl]
    · simp only [nextIControl, h, ↓reduceIte, decodeControl,
        Fin.ofNat?_eq_none_of_not_lt states next h, Option.map_none, nextControl]

/-- Local source steps preserve interpreter shape and control ranges. -/
theorem ICfg.Valid.step {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (ordinary : Turing.MultiTapeTM.Universal.Act)
    (querySymbols : List (Option ℕ)) (answerMoves : List SignType) :
    (cfg.step input d.states ordinary querySymbols answerMoves).Valid d input := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro state hstate
    cases hs : ordinary.state with
    | none => simp [ICfg.step, nextIControl, hs] at hstate
    | some next =>
      simp only [ICfg.step, nextIControl, hs] at hstate
      split at hstate
      next hlt =>
        have heq : next = state := Option.some.inj (Option.some.inj hstate)
        simpa only [← heq] using hlt
      · contradiction
  · simp only [ICfg.step]
    exact moveInput_le h.inputPos ordinary.inputTape
  · simpa only [ICfg.step, length_applyTapes_eq] using h.workTapes
  · simpa only [ICfg.step, List.length_mapIdx] using h.channels

/-- Local halting preserves the storage shape invariant. -/
theorem ICfg.Valid.halt {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) : cfg.halt.Valid d input :=
  ⟨by simp [ICfg.halt], h.inputPos, h.workTapes, h.channels⟩

/-- Installing a reply on a checked channel preserves interpreter shape and ranges. -/
theorem ICfg.Valid.receive {d : Desc} {input : List ℕ} {cfg : ICfg} {r : ℕ}
    (h : cfg.Valid d input) (operation : Fin r)
    {next : ℕ} (hnext : next < d.states) (reply : List ℕ) :
    (cfg.receive operation next reply).Valid d input := by
  refine ⟨?_, h.inputPos, h.workTapes, ?_⟩
  · intro state hstate
    have heq : state = next := by
      have : next = state := by
        simpa [ICfg.receive] using Option.some.inj (Option.some.inj hstate)
      exact this.symm
    simpa only [heq] using hnext
  simpa only [ICfg.receive, List.length_modify] using h.channels

private theorem getD_applyTapes (tapes : List Turing.MultiTapeTM.Universal.Tape)
    (actions : List TapeAct) (index : ℕ) (hindex : index < tapes.length) :
    (applyTapes tapes actions).getD index blankTape =
      (tapes.getD index blankTape).apply (actions.getD index (none, 0)) := by
  induction tapes generalizing actions index with
  | nil => simp at hindex
  | cons tape tapes ih =>
    cases index with
    | zero =>
      cases actions <;> simp [applyTapes, blankTape, Turing.MultiTapeTM.Universal.Tape.apply,
        Turing.MultiTapeTM.Universal.Tape.move]
    | succ index =>
      cases actions with
      | nil =>
        simp only [applyTapes, List.getD_cons_succ, List.getD_nil]
        simp [blankTape, Turing.MultiTapeTM.Universal.Tape.apply,
          Turing.MultiTapeTM.Universal.Tape.move]
      | cons action actions =>
        simp only [applyTapes, List.getD_cons_succ]
        exact ih actions index (by simpa using hindex)

/-- First-order local execution is exactly native `Config.step`. -/
theorem ICfg.toConfig_step {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (ordinary : Turing.MultiTapeTM.Universal.Act)
    (querySymbols : List (Option ℕ)) (answerMoves : List SignType) :
    (cfg.step input d.states ordinary querySymbols answerMoves).toConfig d input =
      (cfg.toConfig d input).step (localAction d.tapes d.states ordinary)
        (fun operation => querySymbols.getD operation.val none)
        (fun operation => answerMoves.getD operation.val 0) := by
  apply Config.ext
  · apply Cfg.ext
    · exact decodeControl_nextIControl d.states ordinary.state
    · apply Fin.ext
      simp only [ICfg.toConfig, ICfg.step, Config.step, Action.apply_inputPos, localAction]
      simp only [min_eq_left h.inputPos]
      have hip : cfg.inputPos < input.length + 2 := by
        have hpos := h.inputPos
        omega
      change min (moveInput cfg.inputPos
          (Turing.MultiTapeTM.Universal.inputSymbol input cfg.inputPos) ordinary.inputTape)
        (input.length + 1) = _
      rw [min_eq_left (moveInput_le h.inputPos ordinary.inputTape)]
      exact moveInput_val (x := input) (p := ⟨cfg.inputPos, hip⟩) ordinary.inputTape
    · funext tape position
      simp only [ICfg.toConfig, ICfg.step, Config.step, localAction,
        Action.apply_workTapes]
      rw [getD_applyTapes _ _ tape.val (by simp [h.workTapes])]
      simp only [Turing.MultiTapeTM.Universal.Tape.apply,
        Turing.MultiTapeTM.Universal.Tape.cellAt_move]
      cases hw : (ordinary.workTapes.getD tape.val (none, 0)).1 with
      | none => simp only [Option.elim_none]
      | some symbol =>
        simp only [Option.elim_some, Turing.MultiTapeTM.Universal.Tape.cellAt_write,
          Function.update_apply]
    · funext tape
      simp only [ICfg.toConfig, ICfg.step, Config.step, localAction,
        Action.apply_workTapePos]
      rw [getD_applyTapes _ _ tape.val (by simp [h.workTapes])]
      simp only [Turing.MultiTapeTM.Universal.Tape.apply,
        Turing.MultiTapeTM.Universal.Tape.head_move]
      cases (ordinary.workTapes.getD tape.val (none, 0)).1 <;> rfl
    · rfl
  · funext operation
    simp only [ICfg.toConfig, ICfg.step, Config.step]
    have hop : operation.val < cfg.channels.length := by
      simpa only [h.channels] using operation.isLt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hop, Channel.step,
      Channel.blank]

/-- First-order local halting is exactly the native description's halting action. -/
theorem ICfg.toConfig_halt {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) :
    cfg.halt.toConfig d input =
      (cfg.toConfig d input).step
        { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := none }
        (fun _ => none) (fun _ => 0) := by
  apply Config.ext
  · apply Cfg.ext
    · rfl
    · apply Fin.ext
      simp [ICfg.toConfig, ICfg.halt, Config.step, h.inputPos, moveInputPos_zero]
    · rfl
    · funext tape
      simp [ICfg.toConfig, ICfg.halt, Config.step, Action.apply_workTapePos]
    · simp [ICfg.toConfig, ICfg.halt, Config.step]
  · funext operation
    simp only [ICfg.toConfig, ICfg.halt, Config.step]
    have hop : operation.val < cfg.channels.length := by
      simpa only [h.channels] using operation.isLt
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hop]

/-- Installing a reply in first-order storage is exactly native query reception. -/
theorem ICfg.toConfig_receive {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (operation : Fin d.operations) {next : ℕ}
    (hnext : next < d.states) (reply : List ℕ) :
    (cfg.receive operation next reply).toConfig d input =
      (cfg.toConfig d input).receive operation (some ⟨next, hnext⟩) reply := by
  apply Config.ext
  · apply Cfg.ext
    · simp only [ICfg.toConfig, ICfg.receive, decodeControl,
        Fin.ofNat?_eq_some_of_lt d.states next hnext, Option.map_some, Config.receive]
    · apply Fin.ext
      simp only [ICfg.toConfig, ICfg.receive, Config.receive]
    · rfl
    · rfl
    · rfl
  · funext other
    simp only [ICfg.toConfig, ICfg.receive, Config.receive]
    by_cases heq : other = operation
    · subst other
      have hop : operation.val < cfg.channels.length := by
        simpa only [h.channels] using operation.isLt
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hop,
        Channel.receive, Channel.blank]
    · have hother : other.val < cfg.channels.length := by
        simpa only [h.channels] using other.isLt
      have hval : other.val ≠ operation.val := fun hval => heq (Fin.ext hval)
      rw [Function.update_of_ne heq]
      simp [List.getD_eq_getElem?_getD,
        List.getElem?_modify_ne (fun _ => Channel.receive reply) cfg.channels hval.symm,
        List.getElem?_eq_getElem hother]

/-- The first-order lookup key is exactly the key observed by the native denotation. -/
theorem ICfg.key_toConfig {d : Desc} {input : List ℕ} {cfg : ICfg}
    (h : cfg.Valid d input) (state : ℕ) :
    cfg.key input state =
      Turing.MultiTapePTM.Universal.key state (cfg.toConfig d input).tapes.inputSymbol
        (cfg.toConfig d input).tapes.workTapeSymbols
        (cfg.toConfig d input).answerSymbols := by
  unfold ICfg.key Turing.MultiTapePTM.Universal.key
  simp only [Key.mk.injEq, Turing.MultiTapeTM.Universal.Key.mk.injEq, true_and]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have hinput := inputSymbol_val (cfg.toConfig d input).tapes
    simpa only [ICfg.key, ICfg.inputSymbol, ICfg.toConfig, min_eq_left h.inputPos] using hinput
  · apply List.ext_getElem
    · simp only [ICfg.workSymbols, List.length_map, List.length_ofFn]
      exact h.workTapes
    · intro index hleft hright
      have hindex : index < d.tapes := by
        simpa only [List.length_ofFn] using hright
      simp only [ICfg.workSymbols, List.getElem_map, List.getElem_ofFn,
        ICfg.toConfig, Cfg.workTapeSymbols]
      rw [List.getD_eq_getElem _ _ (by rw [h.workTapes]; exact hindex)]
      exact Turing.MultiTapeTM.Universal.Tape.read_eq _
  · apply List.ext_getElem
    · simp only [ICfg.answerSymbols, List.length_map, List.length_ofFn]
      exact h.channels
    · intro index hleft hright
      have hindex : index < d.operations := by
        simpa only [List.length_ofFn] using hright
      simp only [ICfg.answerSymbols, List.getElem_map, List.getElem_ofFn,
        ICfg.toConfig, Config.answerSymbols,
        Turing.MultiTapeMachine.Channel.answerSymbol]
      rw [List.getD_eq_getElem _ _ (by rw [h.channels]; exact hindex)]
      rfl

/-- One decoded source instruction either finishes locally or submits a checked finite-channel
request. The successor configuration stored in a query has not installed its reply yet. -/
inductive Command (r : ℕ) where
  /-- No external call. -/
  | local (next : ICfg)
  /-- Submit `request` on a validated channel, then resume in `next`. -/
  | query (operation : Fin r) (request : List ℕ) (next : ℕ) (cfg : ICfg)
deriving Inhabited

/-- Encoding of one interpreted instruction. -/
def eOperation (r : ℕ) : Fin r ↪ List Bool :=
  ⟨fun operation => encUnary operation.val, fun _ _ h => Fin.ext (encUnary.injective h)⟩

/-- A plain sum representation of interpreted instructions. -/
def Command.equivSum (r : ℕ) :
    Command r ≃ ICfg ⊕ (Fin r × List ℕ × ℕ × ICfg) where
  toFun
    | .local cfg => .inl cfg
    | .query operation request next cfg => .inr (operation, request, next, cfg)
  invFun
    | .inl cfg => .local cfg
    | .inr (operation, request, next, cfg) => .query operation request next cfg
  left_inv command := by cases command <;> rfl
  right_inv command := by rcases command with cfg | ⟨operation, request, next, cfg⟩ <;> rfl

/-- Injective encoding of interpreted instructions. -/
def eCommand (r : ℕ) : Command r ↪ List Bool :=
  encOfEquiv (Command.equivSum r)
    (encSum eICfg (encPair (eOperation r)
      (encPair (encList encUnary) (encPair encUnary eICfg))))

/-- Interpret one selected first-order action. Every operation and successor tag is validated
before a query can expose a `Fin r` channel. -/
def ICfg.command (r : ℕ) (d : Desc) (input : List ℕ) (cfg : ICfg) (action : Act) :
    Command r :=
  match action with
  | .step ordinary querySymbols answerMoves =>
      .local (cfg.step input d.states ordinary querySymbols answerMoves)
  | .query operation next =>
      if _hcount : d.operations = r then
        if hop : operation < r then
          if _hnext : next < d.states then
            .query ⟨operation, hop⟩ (cfg.channels.getD operation .blank).query next cfg
          else .local cfg.halt
        else .local cfg.halt
      else .local cfg.halt

/-- Decode and interpret the transition selected by `coin`. A halted configuration is unchanged;
the trap control and a missing table entry halt locally. -/
def ICfg.commandAt (r : ℕ) (d : Desc) (input : List ℕ) (cfg : ICfg)
    (coin : Bool) : Command r :=
  match cfg.control with
  | none => .local cfg
  | some none => .local cfg.halt
  | some (some state) =>
      match d.table.find? (·.1 = cfg.key input state) with
      | none => .local cfg.halt
      | some entry => cfg.command r d input (entry.2.get coin)

end Turing.MultiTapePTM.Universal
