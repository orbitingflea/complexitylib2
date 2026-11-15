/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# A construction-defined quantum-oracle circuit generator

An explicit four-state machine generates the exact descriptions of a nonconstant family of
instruction-free circuits. Its universal-machine description is finite data, rather than a
machine selected from the existential native-computability proof.
-/

public section

namespace CslibFrontierTests.QuantumOracleGenerator

open Cslib Cslib.Quantum Turing Turing.MultiTapeTM
open Cslib.Quantum.UniformOracleCircuitFamily

/-- An instruction-free circuit whose active width is exactly the encoded classical input size. -/
def emptyDescription (n ℓ : ℕ) : OracleCircuitDescription where
  width := 2 * n + 1 + ℓ
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := 0
  instructions := []

private theorem emptyDescription_computableInPolyTime :
    ComputableInPolyTime
      (fun s : OracleInputSize => emptyDescription s.securityParameter s.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription := by
  unfold emptyDescription
  fun_prop

/-- The nonconstant instruction-free family generated below. -/
def emptyFamily : UniformOracleCircuitFamily where
  description := emptyDescription
  computableInPolyTime_description := emptyDescription_computableInPolyTime
  wellFormed n ℓ := by
    constructor <;> simp [emptyDescription]

/-- Two scanning states and two trailing-zero states for the explicit generator. -/
abbrev EmptyGeneratorState := Fin 4

/-- Fixed numbering of the generator's four states. -/
def encEmptyGeneratorState : EmptyGeneratorState ↪ ℕ := Fin.valEmbedding

/-- Emit two `true` bits per input bit, then five `false` bits. -/
def emptyGeneratorTransition (q : EmptyGeneratorState) (input : Option Bool) :
    Action 0 Bool EmptyGeneratorState :=
  if q = 0 then
      match input with
      | some _ =>
          { inputTape := 0, workTapes := Fin.elim0, output := some true,
            state := some 1 }
      | none =>
          { inputTape := -1, workTapes := Fin.elim0, output := some false,
            state := some 2 }
  else if q = 1 then
      match input with
      | some _ =>
          { inputTape := 1, workTapes := Fin.elim0, output := some true,
            state := some 0 }
      | none =>
          { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }
  else if q = 2 then
      match input with
      | some _ =>
          { inputTape := 1, workTapes := Fin.elim0, output := some false,
            state := some 2 }
      | none =>
          { inputTape := -1, workTapes := Fin.elim0, output := some false,
            state := some 3 }
  else
      match input with
      | some _ =>
          { inputTape := 1, workTapes := Fin.elim0, output := some false,
            state := some 3 }
      | none =>
          { inputTape := 0, workTapes := Fin.elim0, output := some false, state := none }

/-- The construction-defined native generator. -/
def emptyGenerator : MultiTapeTM 0 Bool EmptyGeneratorState :=
  .ofTr 0 fun q input _ => emptyGeneratorTransition q input

/-- The finite state/input pairs of `emptyGenerator`, in a fixed inspectable order. -/
def emptyGeneratorKeys : List (EmptyGeneratorState × Option Bool) :=
  [(0, none), (0, some false), (0, some true),
    (1, none), (1, some false), (1, some true),
    (2, none), (2, some false), (2, some true),
    (3, none), (3, some false), (3, some true)]

/-- A literal finite transition table for `emptyGenerator`. -/
def emptyGeneratorCode : Universal.Desc :=
  ⟨0, 0, emptyGeneratorKeys.map fun e =>
    (Universal.key e.1 (e.2.map Universal.eBit) Fin.elim0,
      Universal.Act.ofAction
        ((emptyGeneratorTransition e.1 e.2).map encEmptyGeneratorState Universal.eBit))⟩

private theorem emptyGeneratorCode_holds (q : EmptyGeneratorState) (input : Option Bool)
    (work : Fin 0 → Option Bool) :
    emptyGeneratorCode.Holds (emptyGenerator.map encEmptyGeneratorState Universal.eBit)
      (encEmptyGeneratorState q) (input.map Universal.eBit)
        (Option.map Universal.eBit ∘ work) := by
  rw [show (Option.map Universal.eBit ∘ work) = (Fin.elim0 : Fin 0 → Option ℕ) from
    Subsingleton.elim _ _]
  rw [Universal.Desc.holds_iff]
  rw [show (emptyGenerator.map encEmptyGeneratorState Universal.eBit).tr
      (encEmptyGeneratorState q) (input.map Universal.eBit) Fin.elim0 =
        (emptyGeneratorTransition q input).map encEmptyGeneratorState Universal.eBit by
    have hwork : (Fin.elim0 : Fin 0 → Option ℕ) =
        Option.map Universal.eBit ∘ (Fin.elim0 : Fin 0 → Option Bool) :=
      Subsingleton.elim _ _
    rw [hwork, MultiTapeTM.tr_map, emptyGenerator, MultiTapeTM.tr_ofTr]]
  fin_cases q <;> all_goals
    cases input with
    | none =>
      simp [emptyGeneratorCode, emptyGeneratorKeys, encEmptyGeneratorState,
        Universal.key, emptyGeneratorTransition]
    | some b =>
      cases b <;> simp [emptyGeneratorCode, emptyGeneratorKeys, encEmptyGeneratorState,
        Universal.key, emptyGeneratorTransition]

private theorem simulate_emptyGeneratorCode (input : List Bool) (t : ℕ) :
    Universal.simulate emptyGeneratorCode (input.map Universal.eBit) t =
      ((emptyGenerator.runFrom (emptyGenerator.initCfg input) t).output.map Universal.eBit,
        (emptyGenerator.runFrom (emptyGenerator.initCfg input) t).state.isNone) :=
  Universal.simulate_of_holds encEmptyGeneratorState Universal.eBit emptyGenerator
    emptyGeneratorCode rfl rfl emptyGeneratorCode_holds input t

private def scanCfg (input : List Bool) (n : ℕ) (hn : n ≤ input.length) :
    Cfg 0 Bool EmptyGeneratorState input :=
  ⟨some 0, ⟨n + 1, by omega⟩, fun _ _ => none, fun _ => 0,
    List.replicate (2 * n) true⟩

private def secondCfg (input : List Bool) (n : ℕ) (hn : n < input.length) :
    Cfg 0 Bool EmptyGeneratorState input :=
  ⟨some 1, ⟨n + 1, by omega⟩, fun _ _ => none, fun _ => 0,
    List.replicate (2 * n) true ++ [true]⟩

private theorem step_scan (input : List Bool) (n : ℕ) (hn : n < input.length) :
    emptyGenerator.step (scanCfg input n hn.le) = secondCfg input n hn := by
  have hsym : (scanCfg input n hn.le).inputSymbol = some input[n] :=
    inputSymbolInner n (by simp [scanCfg, Nat.add_comm]) hn
  rw [step_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes <;>
    simp [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, secondCfg]

private theorem step_second (input : List Bool) (n : ℕ) (hn : n < input.length) :
    emptyGenerator.step (secondCfg input n hn) = scanCfg input (n + 1) (by omega) := by
  have hsym : (secondCfg input n hn).inputSymbol = some input[n] :=
    inputSymbolInner n (by simp [secondCfg, Nat.add_comm]) hn
  have hmove : moveInputPos (⟨n + 1, by omega⟩ : Fin (input.length + 2)) 1 =
      ⟨n + 2, by omega⟩ := by
    simpa [Nat.add_assoc] using moveInputPos_pos_of_ne_right
      (⟨n + 1, by omega⟩ : Fin (input.length + 2)) (by simp; omega)
  rw [step_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, secondCfg]
  · simpa [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, secondCfg] using hmove
  · simp only [Fin.isValue, Action.apply_output]
    rw [emptyGenerator, MultiTapeTM.tr_ofTr]
    change (List.replicate (2 * n) true ++ [true]) ++ [true] =
      List.replicate (2 * (n + 1)) true
    rw [show 2 * (n + 1) = 2 * n + 2 by omega, List.replicate_add]
    simp only [List.reduceReplicate, List.append_assoc, List.singleton_append]

private theorem runFrom_scan (input : List Bool) (n : ℕ) (hn : n ≤ input.length) :
    emptyGenerator.runFrom (emptyGenerator.initCfg input) (2 * n) = scanCfg input n hn := by
  induction n with
  | zero => exact Cfg.ext_zero_tapes rfl rfl rfl
  | succ n ih =>
    have hnlt : n < input.length := by omega
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, runFrom,
      Function.iterate_add_apply]
    change emptyGenerator.step^[2]
      (emptyGenerator.runFrom (emptyGenerator.initCfg input) (2 * n)) = _
    rw [ih (by omega)]
    change emptyGenerator.step (emptyGenerator.step (scanCfg input n (by omega))) = _
    rw [step_scan input n hnlt, step_second input n hnlt]

private def tailInnerCfg (input : List Bool) (q : EmptyGeneratorState) (zeros : ℕ)
    (_hinput : 0 < input.length) :
    Cfg 0 Bool EmptyGeneratorState input :=
  ⟨some q, ⟨input.length, by omega⟩, fun _ _ => none, fun _ => 0,
    List.replicate (2 * input.length) true ++ List.replicate zeros false⟩

private def tailBoundaryCfg (input : List Bool) (q : Option EmptyGeneratorState) (zeros : ℕ) :
    Cfg 0 Bool EmptyGeneratorState input :=
  ⟨q, ⟨input.length + 1, by omega⟩, fun _ _ => none, fun _ => 0,
    List.replicate (2 * input.length) true ++ List.replicate zeros false⟩

private theorem moveInputPos_rightBoundary_left (input : List Bool) :
    moveInputPos (⟨input.length + 1, by omega⟩ : Fin (input.length + 2)) (-1) =
      ⟨input.length, by omega⟩ := by
  apply moveInputPos_neg_of_ne_left
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_zero] at hval
  omega

private theorem moveInputPos_lastCell_right (input : List Bool) :
    moveInputPos (⟨input.length, by omega⟩ : Fin (input.length + 2)) 1 =
      ⟨input.length + 1, by omega⟩ := by
  apply moveInputPos_pos_of_ne_right
  intro h
  change input.length = input.length + 1 at h
  omega

private theorem step_scan_boundary (input : List Bool) (hinput : 0 < input.length) :
    emptyGenerator.step (scanCfg input input.length le_rfl) =
      tailInnerCfg input 2 1 hinput := by
  have hblank : (scanCfg input input.length le_rfl).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [scanCfg]))
  rw [step_of_state rfl, hblank]
  apply Cfg.ext_zero_tapes
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, tailInnerCfg]
  · simpa [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, tailInnerCfg] using
      moveInputPos_rightBoundary_left input
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, scanCfg, tailInnerCfg]

private theorem step_tail_two (input : List Bool) (hinput : 0 < input.length) :
    emptyGenerator.step (tailInnerCfg input 2 1 hinput) =
      tailBoundaryCfg input (some 2) 2 := by
  have hsym : (tailInnerCfg input 2 1 hinput).inputSymbol =
      some input[input.length - 1] :=
    inputSymbolInner (input.length - 1) (by simp [tailInnerCfg]; omega) (by omega)
  rw [step_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
  · simpa [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
      using moveInputPos_lastCell_right input
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]

private theorem step_tail_three (input : List Bool) (hinput : 0 < input.length) :
    emptyGenerator.step (tailBoundaryCfg input (some 2) 2) =
      tailInnerCfg input 3 3 hinput := by
  have hblank : (tailBoundaryCfg input (some 2) 2).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [tailBoundaryCfg]))
  rw [step_of_state rfl, hblank]
  apply Cfg.ext_zero_tapes
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
  · simpa [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
      using moveInputPos_rightBoundary_left input
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]

private theorem step_tail_four (input : List Bool) (hinput : 0 < input.length) :
    emptyGenerator.step (tailInnerCfg input 3 3 hinput) =
      tailBoundaryCfg input (some 3) 4 := by
  have hsym : (tailInnerCfg input 3 3 hinput).inputSymbol =
      some input[input.length - 1] :=
    inputSymbolInner (input.length - 1) (by simp [tailInnerCfg]; omega) (by omega)
  rw [step_of_state rfl, hsym]
  apply Cfg.ext_zero_tapes
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
  · simpa [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]
      using moveInputPos_lastCell_right input
  · simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailInnerCfg, tailBoundaryCfg]

private theorem step_tail_five (input : List Bool) :
    emptyGenerator.step (tailBoundaryCfg input (some 3) 4) =
      tailBoundaryCfg input none 5 := by
  have hblank : (tailBoundaryCfg input (some 3) 4).inputSymbol = none :=
    inputSymbol_eq_none_of_boundary (Or.inr (by simp [tailBoundaryCfg]))
  rw [step_of_state rfl, hblank]
  apply Cfg.ext_zero_tapes <;>
    simp [emptyGenerator, emptyGeneratorTransition, Action.apply, tailBoundaryCfg]

private theorem runFrom_full (input : List Bool) (hinput : 0 < input.length) :
    emptyGenerator.runFrom (emptyGenerator.initCfg input) (2 * input.length + 5) =
      ⟨none, ⟨input.length + 1, by omega⟩, fun _ _ => none, fun _ => 0,
        List.replicate (2 * input.length) true ++ List.replicate 5 false⟩ := by
  rw [show 2 * input.length + 5 = 5 + 2 * input.length by omega, runFrom,
    Function.iterate_add_apply]
  change emptyGenerator.step^[5]
    (emptyGenerator.runFrom (emptyGenerator.initCfg input) (2 * input.length)) = _
  rw [runFrom_scan input input.length le_rfl]
  change emptyGenerator.step (emptyGenerator.step (emptyGenerator.step
    (emptyGenerator.step (emptyGenerator.step (scanCfg input input.length le_rfl))))) = _
  rw [step_scan_boundary input hinput, step_tail_two input hinput,
    step_tail_three input hinput, step_tail_four input hinput, step_tail_five]
  rfl

private theorem flatMap_replicate_true (n : ℕ) :
    (List.replicate n true).flatMap (fun b => [true, b]) =
      List.replicate (2 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, List.flatMap_cons, ih]
    rw [show 2 * (n + 1) = 2 + 2 * n by omega, List.replicate_add]
    rfl

private theorem enc_emptyDescription (input : OracleInputSize) :
    encOracleCircuitDescription
        (emptyDescription input.securityParameter input.classicalInputLength) =
      List.replicate (2 * (encOracleInputSize input).length) true ++
        List.replicate 5 false := by
  rcases input with ⟨n, ℓ⟩
  simp only [emptyDescription, encOracleCircuitDescription_apply,
    encOracleCircuitDescriptionFields, encOracleInputSize_apply, encOracleInputSizeFields,
    encPair_apply, encUnary_apply, encList_nil, frame, flatMap_replicate_true,
    List.append_nil, List.length_append, List.length_replicate]
  simp only [List.length_singleton, Nat.mul_zero, List.replicate_zero, List.nil_append,
    List.append_assoc, List.reduceReplicate, List.singleton_append]

/-- The explicit generator certificate, with linear time and zero workspace. -/
def emptyGeneratorCertificate : emptyFamily.GeneratorCertificate where
  code := emptyGeneratorCode
  time m := 2 * m + 5
  workspace _ := 0
  time_polynomiallyBounded := by fun_prop
  workspace_polynomiallyBounded := by fun_prop
  computes input := by
    have hinput : 0 < (encOracleInputSize input).length := by
      rcases input with ⟨n, ℓ⟩
      simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
        encUnary_apply, List.length_replicate]
      omega
    rw [simulate_emptyGeneratorCode, runFrom_full _ hinput]
    change (List.map Universal.eBit
      (List.replicate (2 * (encOracleInputSize input).length) true ++
        List.replicate 5 false), true) = _
    rw [← enc_emptyDescription]
    rfl
  workspace_le input := by
    simp [Universal.simSpace, emptyGeneratorCode]

-- The client is nonconstant in both its finite description and its encoded output.
example : (emptyFamily.description 0 0).width ≠ (emptyFamily.description 1 0).width := by decide

example : (encOracleCircuitDescription (emptyFamily.description 0 0)).length <
    (encOracleCircuitDescription (emptyFamily.description 1 0)).length := by decide

-- The literal static program and all dynamic coordinates have inspectable exact values.
-- Reducing the twelve-entry encoded transition table needs more recursion than Lean's default.
set_option maxRecDepth 10000 in
/-- The literal generator descriptor has exactly 592 bits in the universal encoding. -/
theorem length_eDesc_emptyGeneratorCode :
    (Universal.eDesc emptyGeneratorCode).length = 592 := by decide

/-- The certificate exposes the same exact static size on every input. -/
theorem emptyGeneratorResources_codeBits (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).codeBits = 592 :=
  length_eDesc_emptyGeneratorCode

/-- The exact native time coordinate is two steps per input bit plus the five-bit suffix. -/
theorem emptyGeneratorResources_time (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).time =
      2 * (encOracleInputSize input).length + 5 := by
  simp only [GeneratorCertificate.resources, emptyGeneratorCertificate]

/-- The zero-work-tape generator uses no visited workspace. -/
theorem emptyGeneratorResources_workspace (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).workspace = 0 := by
  simp only [GeneratorCertificate.resources, emptyGeneratorCertificate]

/-- The exact generated description has two bits per input bit and five suffix bits. -/
theorem emptyGeneratorResources_outputBits (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).outputBits =
      2 * (encOracleInputSize input).length + 5 := by
  simp only [GeneratorCertificate.resources]
  change (encOracleCircuitDescription
    (emptyDescription input.securityParameter input.classicalInputLength)).length = _
  rw [enc_emptyDescription]
  simp

/-- This particular streaming generator emits one output bit per charged native step. -/
theorem emptyGeneratorResources_time_eq_outputBits (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).time =
      (emptyGeneratorCertificate.resources input).outputBits := by
  rw [show (emptyGeneratorCertificate.resources input).time =
      2 * (encOracleInputSize input).length + 5 from rfl]
  simp only [GeneratorCertificate.resources]
  change 2 * (encOracleInputSize input).length + 5 =
    (encOracleCircuitDescription
      (emptyDescription input.securityParameter input.classicalInputLength)).length
  rw [enc_emptyDescription]
  simp

/-- The scalar offline accounting cost charges static code, time, workspace and emitted bits. -/
theorem emptyGeneratorResources_total (input : OracleInputSize) :
    (emptyGeneratorCertificate.resources input).total =
      4 * (encOracleInputSize input).length + 602 := by
  simp only [GeneratorResources.total]
  rw [emptyGeneratorResources_codeBits, emptyGeneratorResources_time,
    emptyGeneratorResources_workspace, emptyGeneratorResources_outputBits]
  omega

-- One fixed program produces two different exact descriptions at its stated finite bounds.
example :
    Universal.simulate emptyGeneratorCertificate.code
        (List.map Universal.eBit (encOracleInputSize ⟨0, 0⟩)) 7 =
      (List.map Universal.eBit (encOracleCircuitDescription (emptyFamily.description 0 0)), true) :=
  emptyGeneratorCertificate.computes ⟨0, 0⟩

example :
    Universal.simulate emptyGeneratorCertificate.code
        (List.map Universal.eBit (encOracleInputSize ⟨1, 0⟩)) 11 =
      (List.map Universal.eBit (encOracleCircuitDescription (emptyFamily.description 1 0)), true) :=
  emptyGeneratorCertificate.computes ⟨1, 0⟩

-- A polynomial family of encoded inputs has a componentwise polynomial generator schedule.
example : GeneratorResources.IsPolynomial
    (fun n => emptyGeneratorCertificate.resources ⟨n, n + 1⟩) := by
  apply emptyGeneratorCertificate.resources_isPolynomial
  simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
    encUnary_apply, List.length_replicate]
  fun_prop

-- The explicit scalar sum is polynomial as a consequence of the componentwise certificate.
example : PolynomiallyBounded
    (fun n => (emptyGeneratorCertificate.resources ⟨n, n + 1⟩).total) := by
  apply GeneratorResources.IsPolynomial.total
  apply emptyGeneratorCertificate.resources_isPolynomial
  simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
    encUnary_apply, List.length_replicate]
  fun_prop

-- Componentwise addition composes two separately stored artifacts. It is deliberately not used
-- for two runs of `emptyGeneratorCertificate`, which would charge its identical static code twice.
example {r s : ℕ → GeneratorResources} (hr : GeneratorResources.IsPolynomial r)
    (hs : GeneratorResources.IsPolynomial s) :
    GeneratorResources.IsPolynomial (fun n => r n + s n) :=
  hr.add hs

end CslibFrontierTests.QuantumOracleGenerator
