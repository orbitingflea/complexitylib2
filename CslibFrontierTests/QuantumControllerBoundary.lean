/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.ProgramSemantics
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Boundary
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.RandomOracle
public import CslibFrontierTests.QuantumControllerFixture
public import CslibFrontierTests.QuantumOracleInteraction
import CslibFrontierTests.QuantumCircuitFixture

/-!
A fixed-layout native specialization of the accepted one-boundary example. The eight-qubit
device preallocates the first stage's three memory wires at positions 5, 6 and 7. Its request
wires 5 and 6 stay zero, while wire 7 remains coherent through the classical service call.
The accepted-status bit at wire 3 is known in this specialization. The service key controls
wire 4 before the existing second-stage circuit runs. This is an actual native word program;
it is not a general relocation or initialization compiler for arbitrary stage families.
-/

public section

namespace CslibFrontierTests.QuantumControllerBoundary

open Cslib Cslib.Quantum Cslib.Probability Turing.MultiTapeTM
open DeviceProgram QuantumControllerFixture QuantumOracleInteraction

abbrev Operation := DeviceOperation ⊕ Unit
abbrev Hash := QuantumOracleDecapsulation.Hash

/-- The same accepted toy decapsulation service as the native one-boundary fixture. Short
requests are padded with false and longer requests use their first two bits. -/
noncomputable def service (H : Hash) : Unit × List Bool → StateT Unit PMF (Fin 2 → Bool) :=
  fun request state => (fixedService H (fun i => request.2.getD i.val false)).map
    (fun reply => (reply, state))

/-- Read only the second bit of the two-bit accepted reply; empty and one-bit replies select
false. The native certificate still quantifies over every possible external word oracle. -/
@[expose] def requestKey : WordOracleComp Operation Bool :=
  (fun reply => reply.tail.headD false) <$>
    (List.take 2 <$> ProbOracleComp.query (.inr (), [false, false]))

@[expose] def prepare : WordOracleComp Operation Unit := do
  gate (false, false, 3, [])
  gate (false, true, 7, [])

@[expose] def initializeKey (key : Bool) : WordOracleComp Operation Unit :=
  if key then gate (false, false, 4, []) else pure ()

@[expose] def finish (key : Bool) : WordOracleComp Operation Unit := do
  initializeKey key
  gate (false, true, 7, [])
  command (.inl .query) []
  gate (false, false, 1, [4])

/-- The request is known to be zero for this fixed native input, so the two outcomes are
discarded after reading the physical request wires. The continuation depends on the service key. -/
@[expose] def program (_n : ℕ) (_input : List Bool) : WordOracleComp Operation Unit := do
  prepare
  let _ ← requestBit (.inl .measure) (encUnary 5)
  let _ ← requestBit (.inl .measure) (encUnary 6)
  let key ← requestKey
  finish key

private theorem isOraclePPTOn_requestKey {α : Type} (input : α ↪ List Bool) :
    IsOraclePPTOn input encBool (fun _ => requestKey) := by
  unfold requestKey
  exact (IsOraclePPTOn.query_take' (Operation := Operation) (.inr ())
    (.const [false, false]) (.const 2)).map' (by fun_prop)

theorem isOraclePPTOn_finish : IsOraclePPTOn encBool encUnit finish := by
  have hkey : IsOraclePPTOn encBool encUnit initializeKey :=
    IsOraclePPTOn.cond' ComputableInPolyTime.id' (isOraclePPTOn_gate encBool _)
      (ComputableInPolyTime.const ()).isOraclePPTOn
  unfold finish
  apply hkey.bind
  exact (isOraclePPTOn_gate encUnit _).bind
    ((isOraclePPTOn_command encUnit _ _).bind (isOraclePPTOn_gate encUnit _))

/-- One native certificate covers the complete physical controller, including its service call
and the branch selected by its bounded reply. -/
theorem isOraclePPT_program : IsOraclePPT encUnit program := by
  have hprepare {α : Type} (input : α ↪ List Bool) :
      IsOraclePPTOn input encUnit (fun _ => prepare) :=
    (isOraclePPTOn_gate input _).bind (isOraclePPTOn_gate encUnit _)
  apply IsOraclePPTOn.isOraclePPT
  unfold program
  apply (hprepare (encPair encUnary encBits)).bind
  apply (isOraclePPTOn_requestBit encUnit (.inl .measure) (.const (encUnary 5))).bind
  apply (isOraclePPTOn_requestBit encBool (.inl .measure) (.const (encUnary 6))).bind
  exact (isOraclePPTOn_requestKey encBool).bind isOraclePPTOn_finish

noncomputable def x₃ : PlacedGate 8 := ⟨1, Gate.not, ⟨![3], by decide⟩⟩
noncomputable def x₄ : PlacedGate 8 := ⟨1, Gate.not, ⟨![4], by decide⟩⟩

noncomputable def initial : DeviceState 8 Unit Unit :=
  pureDevice (ket (fun _ => false)) (norm_ket _)

/-- The coherent memory with the preallocated classical prefix. -/
noncomputable def memory (key : Bool) : DeviceState 8 Unit Unit :=
  pureDevice (h₈.eval (ket (baseWord key false))) (by simp)

theorem x₃_initial : x₃.eval (ket (fun _ => false)) = ket (baseWord false false) := by
  have h := GateCode.eval_toPlacedGate_ket (g := x₃) (t := 3) (cs := [])
    (by rfl) (by decide) (fun _ => false)
  rw [h]
  congr 1
  ext i
  fin_cases i <;> simp [baseWord]

theorem h₈_baseWord (key : Bool) :
    h₈.eval (ket (baseWord key false)) =
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (baseWord key false) +
      (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) • ket (baseWord key true) := by
  have h := GateCode.eval_toPlacedGate_hadamard_ket
    (g := h₈) (t := 7) (by rfl) (by decide) (baseWord key false)
  have hu (b : Bool) : Function.update (baseWord key false) (7 : Fin 8) b = baseWord key b := by
    ext i
    fin_cases i <;> simp [baseWord]
  simpa [Fintype.sum_bool, hu, add_comm] using h

theorem x₄_baseWord (key bit : Bool) :
    x₄.eval (ket (baseWord key bit)) = ket (baseWord (!key) bit) := by
  have h := GateCode.eval_toPlacedGate_ket (g := x₄) (t := 4) (cs := [])
    (by rfl) (by decide) (baseWord key bit)
  rw [h]
  congr 1
  ext i
  fin_cases i <;> simp [baseWord]

theorem x₄_memory : (memory false).evolve x₄.matrix = memory true := by
  have hv : x₄.eval (h₈.eval (ket (baseWord false false))) =
      h₈.eval (ket (baseWord true false)) := by
    rw [h₈_baseWord, map_add, map_smul, map_smul, x₄_baseWord, x₄_baseWord]
    exact (h₈_baseWord true).symm
  unfold memory
  rw [pureDevice_evolve_gate]
  simp only [hv]

theorem measure_memory (key : Bool) (wire : Fin 8) (hw : wire = 5 ∨ wire = 6) :
    (memory key).measure (fun x => x wire) = PMF.pure (false, memory key) := by
  unfold memory
  apply pureDevice_measure_eq_pure
  intro x hx
  by_contra h
  have hne (b : Bool) : x ≠ baseWord key b := by
    intro he
    apply h
    rw [he]
    rcases hw with rfl | rfl <;> rfl
  rw [h₈_baseWord] at hx
  simp [hne] at hx

theorem run_prepare (H Hservice : Hash) :
    ProbOracleComp.runWith (deviceWordHandler H (service Hservice)) prepare initial =
      PMF.pure ((), memory false) := by
  simp only [prepare, ProbOracleComp.runWith_bind, runWith_gate, PMF.pure_bind]
  unfold initial
  rw [pureDevice_instruction H _ x₃ (by rfl)]
  simp only [x₃_initial]
  rw [pureDevice_instruction H _ h₈ (by rfl)]
  rfl

theorem run_requestKey (H Hservice : Hash) (s : DeviceState 8 Unit Unit) :
    ProbOracleComp.runWith (deviceWordHandler H (service Hservice)) requestKey s =
      PMF.pure (Hservice (fun _ => false) 0, s) := by
  have hhandler := deviceWordHandler_encode (κ := Unit) H (service Hservice)
    (DeviceRequest.service (m := 8) () [false, false])
  simp only [DeviceRequest.encode] at hhandler
  have hs : service Hservice ((), [false, false]) () =
      PMF.pure (![true, Hservice (fun _ => false) 0], ()) := by
    unfold service
    have hword : (fun i : Fin 2 => [false, false].getD i.val false) = fun _ => false := by
      ext i
      fin_cases i <;> rfl
    rw [hword, fixedService_honest, PMF.pure_map]
  have hstate : { s with serviceState := () } = s := by
    apply DeviceState.ext rfl
    exact Subsingleton.elim _ _
  rw [requestKey, ProbOracleComp.runWith_map, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, hhandler, deviceHandler_service]
  have hu : s.serviceState = () := Subsingleton.elim _ _
  simp [hu, hs, hstate, List.ofFn_succ]

theorem run_initializeKey (H Hservice : Hash) (key : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (service Hservice))
      (initializeKey key) (memory false) =
        PMF.pure ((), memory key) := by
  unfold initializeKey
  cases key
  · simp [ProbOracleComp.runWith_pure]
  · simp only [ite_true, runWith_gate]
    rw [DeviceState.instruction_apply,
      show (OracleGateCode.gate (false, false, 4, [])).toPlacedGate? 8 H = some x₄ by rfl]
    simp only [x₄_memory]

theorem run_finish (H Hservice : Hash) (key : Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (service Hservice)) (finish key) (memory false) =
      PMF.pure ((), pureDevice (ket (answerWord H key false)) (norm_ket _)) := by
  simp only [finish, ProbOracleComp.runWith_bind, run_initializeKey, PMF.pure_bind,
    runWith_gate, runWith_query]
  unfold memory
  rw [pureDevice_instruction H _ h₈ (by rfl)]
  have hh : h₈.eval (h₈.eval (ket (baseWord key false))) = ket (baseWord key false) :=
    QuantumCircuit.hadamard_twice ⟨![7], by decide⟩ _
  simp only [hh]
  rw [pureDevice_instruction H .query
    (xorQuery H (Fin.castLEEmb (by decide : 2 ≤ 8))) (by rfl)]
  simp only [query_baseWord]
  rw [pureDevice_instruction H _ compareReply (by rfl)]
  simp only [compareReply_queriedWord]

/-- The actual native controller realizes the previously checked one-boundary state on its
known preallocated layout. Separate table parameters also support the negative redraw test. -/
theorem run_program (H Hservice : Hash) (n : ℕ) (input : List Bool) :
    ProbOracleComp.runWith (deviceWordHandler H (service Hservice)) (program n input) initial =
      PMF.pure ((), pureDevice (ket (answerWord H (Hservice (fun _ => false) 0) false))
        (norm_ket _)) := by
  simp only [program, ProbOracleComp.runWith_bind, run_prepare, PMF.pure_bind]
  rw [show encUnary 5 = encUnary (5 : Fin 8).val from rfl, runWith_measure,
    measure_memory false 5 (Or.inl rfl), PMF.pure_bind]
  rw [show encUnary 6 = encUnary (6 : Fin 8).val from rfl, runWith_measure,
    measure_memory false 6 (Or.inr rfl), PMF.pure_bind, run_requestKey, PMF.pure_bind, run_finish]

/-- Forgetting the terminal classical value identifies the complete controller density with
`runClassicalQuery`, rather than merely equating one acceptance bit. -/
theorem run_program_density (H Hservice : Hash) (n : ℕ) (input : List Bool) :
    (ProbOracleComp.runWith (deviceWordHandler H (service Hservice))
      (program n input) initial).map (fun p => p.2.density) =
        PMF.pure (nativeState H Hservice) := by
  rw [run_program, PMF.pure_map, pureDevice_density, nativeState_eq]

/-- The saved work qubit is decoded to zero after the genuine classical service boundary. -/
theorem run_program_memory (H Hservice : Hash) (n : ℕ) (input : List Bool) :
    (ProbOracleComp.runWith (deviceWordHandler H (service Hservice))
      (program n input) initial).bind
      (fun p => (POVM.basis.measureDensity p.2.density p.2.isDensityMatrix).map
        (fun z => z.1 7)) = PMF.pure false := by
  rw [run_program, PMF.pure_bind]
  simp only [pureDevice_density, prodState_ket,
    POVM.measureDensity_pureState _ _ (norm_ket _), POVM.measure_basis,
    measure_ket, PMF.pure_map, answerWord_memory]

/-- Read the comparison wire after the complete physical controller. Keeping the two table
arguments explicit also exposes the invalid independent-service redraw experiment below. -/
noncomputable def readProgram (H Hservice : Hash) (n : ℕ) (input : List Bool) : PMF Bool :=
  (ProbOracleComp.runWith (deviceWordHandler H (service Hservice))
    (program n input) initial).bind fun p =>
      (POVM.basis.measureDensity p.2.density p.2.isDensityMatrix).map (fun z => z.1 1)

/-- The controller-level observation is the same observation already calculated for the native
two-stage boundary, for shared or independently redrawn tables. -/
theorem readProgram_eq (H Hservice : Hash) (n : ℕ) (input : List Bool) :
    readProgram H Hservice n input = nativeRead H Hservice 1 := by
  unfold readProgram
  rw [run_program, PMF.pure_bind, nativeRead_eq]
  simp only [pureDevice_density, prodState_ket,
    POVM.measureDensity_pureState _ _ (norm_ket _), POVM.measure_basis,
    measure_ket, PMF.pure_map]

/-- The adapter samples one table and gives it to both the classical service and coherent query
of the actual fixed-layout controller. -/
@[expose] noncomputable def sampledProgram (n : ℕ) (input : List Bool) : PMF Bool :=
  (Quantum.RandomOracle.runWith service (program n input) initial).bind fun p =>
    (POVM.basis.measureDensity p.2.density p.2.isDensityMatrix).map (fun z => z.1 1)

theorem sampledProgram_eq_sharedExperiment (n : ℕ) (input : List Bool) :
    sampledProgram n input = sharedExperiment := by
  rw [sharedExperiment_eq_uniform_bind]
  unfold sampledProgram
  simp only [Quantum.RandomOracle.runWith_eq, PMF.bind_bind]
  congr 1
  funext H
  exact readProgram_eq H H n input

/-- Sharing the adapter's sampled table makes the service/query comparison false certainly. -/
theorem sampledProgram_eq (n : ℕ) (input : List Bool) :
    sampledProgram n input = PMF.pure false := by
  rw [sampledProgram_eq_sharedExperiment, sharedExperiment_eq]

/-- In the negative experiment only the classical service receives an independent table. -/
noncomputable def redrawnProgram (n : ℕ) (input : List Bool) : PMF Bool := do
  let H ← Probability.PMF.uniformOfFintype Hash
  let Hservice ← Probability.PMF.uniformOfFintype Hash
  readProgram H Hservice n input

theorem redrawnProgram_eq_redrawnExperiment (n : ℕ) (input : List Bool) :
    redrawnProgram n input = redrawnExperiment := by
  rw [redrawnExperiment_eq_uniform_bind_bind]
  unfold redrawnProgram
  congr 1
  funext H
  congr 1
  funext Hservice
  exact readProgram_eq H Hservice n input

/-- Redrawing the service table makes the actual controller's comparison bit uniform. -/
theorem redrawnProgram_eq (n : ℕ) (input : List Bool) :
    redrawnProgram n input = Probability.PMF.uniformOfFintype Bool := by
  rw [redrawnProgram_eq_redrawnExperiment, redrawnExperiment_eq]

/-- The genuine controller detects shared-table reuse certainly, while independently redrawing
the service table reduces the same comparison to probability one half. -/
example (n : ℕ) (input : List Bool) :
    sampledProgram n input false = 1 ∧ redrawnProgram n input false = 1 / 2 := by
  rw [sampledProgram_eq, redrawnProgram_eq]
  norm_num [Probability.PMF.uniformOfFintype_apply]

-- A no-query experiment is independent of its table, including at zero input/output widths.
example : Quantum.RandomOracle.sample (a := 0) (b := 0) (fun _ => PMF.pure true) =
    PMF.pure true := by
  simp

end CslibFrontierTests.QuantumControllerBoundary
