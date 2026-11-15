/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Game.AttackResources
import CslibFrontier.Tactic.PolyTime

public section

/-!
# Checked clients for componentwise attack resources

The finite client uses a nonconstant explicit installed-artifact inventory and every execution
coordinate. Adversary, reducer and generic programs stay independent; two generic-program
occurrences verify per-copy charging. Separate handler and table/advice occurrences contrast with a
main program containing hardwired versions, which are not charged again. Ordered, pairwise-distinct
time and workspace sentinels for all thirteen phases catch omissions, duplications and field
substitutions. The family client proves all static, phase and execution coordinates polynomial,
then applies the reusable bridge. Equal games isolate the resource API; this test asserts no
cryptographic security endpoint.
-/

namespace Cslib.Tests.AttackResources

open Cslib Cslib.Crypto
open scoped NNReal

/-- A nonconstant installed inventory. Adversary, reducer and generic programs have different
roles. The two `program` entries are distinct stored copies, so both contribute. -/
def sampleInventory (n : ℕ) : List Game.InstalledArtifact :=
  [{ kind := .adversary, bits := n + 1 },
    { kind := .reducer, bits := 2 * n + 1 },
    { kind := .program, bits := 3 * n + 1 },
    { kind := .program, bits := 4 * n + 1 },
    { kind := .generatedProgram, bits := 5 * n + 1 },
    { kind := .generator, bits := 6 * n + 1 },
    { kind := .compiler, bits := 7 * n + 1 },
    { kind := .interpreter, bits := 8 * n + 1 },
    { kind := .controller, bits := 9 * n + 1 },
    { kind := .handler, bits := 10 * n + 1 },
    { kind := .table, bits := 11 * n + 1 }]

/-- Every online phase has pairwise-distinct, nonconstant time and workspace sentinels. Their
ordered vectors expose field substitutions; their aggregate exposes missing or duplicate time. -/
def sampleOnlinePhases (n : ℕ) : Game.OnlinePhaseLedger where
  inputRead := { time := 17 * (n + 1), workspace := 30 * (n + 1) }
  compiler := { time := 18 * (n + 1), workspace := 31 * (n + 1) }
  compilerOutputCopy := { time := 19 * (n + 1), workspace := 32 * (n + 1) }
  marshalling := { time := 20 * (n + 1), workspace := 33 * (n + 1) }
  tags := { time := 21 * (n + 1), workspace := 34 * (n + 1) }
  dispatch := { time := 22 * (n + 1), workspace := 35 * (n + 1) }
  queryRequest := { time := 23 * (n + 1), workspace := 36 * (n + 1) }
  queryReply := { time := 24 * (n + 1), workspace := 37 * (n + 1) }
  handler := { time := 25 * (n + 1), workspace := 38 * (n + 1) }
  interpreter := { time := 26 * (n + 1), workspace := 39 * (n + 1) }
  controller := { time := 27 * (n + 1), workspace := 40 * (n + 1) }
  outputProduction := { time := 28 * (n + 1), workspace := 41 * (n + 1) }
  outputCopy := { time := 29 * (n + 1), workspace := 42 * (n + 1) }

/-- Executed compiler coordinates used by both separate and inlined installation clients. -/
def sampleCompilerExecution (n : ℕ) : Game.ExecutedCompilerResources where
  inputBits := 2 * n + 1
  outputBits := 5 * n + 1

/-- Full execution coordinates, including initial input and final-output copying. -/
def sampleExecution (n : ℕ) : Game.AttackExecutionResources where
  inputBits := 12 * n + 1
  onlineTime := 299 * n + 299
  onlineWorkspace := 42 * n + 42
  phases := sampleOnlinePhases n
  compiler := sampleCompilerExecution n
  randomBits := 14 * n + 1
  classicalQueries := 15 * n + 1
  quantumQueries := 16 * n + 1
  qubits := 17 * n + 1
  gates := 18 * n + 1
  requestBits := 19 * n + 1
  replyBits := 20 * n + 1
  outputBits := 16 * n + 1

/-- A nonconstant profile exercising every installed, compiler, online, oracle and communication
coordinate. The compiler runs online here: its time is included in `onlineTime`, its workspace fits
the online peak, and its generated program is a distinct installed occurrence. -/
def sampleResources (n : ℕ) : Game.AttackResources :=
  ⟨sampleInventory n, sampleExecution n⟩

/-- Per-kind sums keep adversary and reducer storage separate from both generic-program copies. -/
theorem sampleInstalledBits_at_two :
    (sampleResources 2).adversaryBits = 3 ∧
      (sampleResources 2).reducerBits = 5 ∧
      (sampleResources 2).programBits = 16 ∧
      (sampleResources 2).generatedProgramBits = 11 ∧
      (sampleResources 2).generatorBits = 13 ∧
      (sampleResources 2).compilerBits = 15 ∧
      (sampleResources 2).interpreterBits = 17 ∧
      (sampleResources 2).controllerBits = 19 ∧
      (sampleResources 2).handlerBits = 21 ∧
      (sampleResources 2).tableBits = 23 := by
  decide

/-- The explicit ordered vectors catch substitutions as well as omissions. Their time sum uses
every phase exactly once, while the workspace aggregate is the maximum rather than a sum. -/
theorem sampleOnlineSentinels_at_two :
    (sampleOnlinePhases 2).asList.length = 13 ∧
      (sampleOnlinePhases 2).asList.map (fun phase => phase.time) =
        [51, 54, 57, 60, 63, 66, 69, 72, 75, 78, 81, 84, 87] ∧
      (sampleOnlinePhases 2).asList.map (fun phase => phase.workspace) =
        [90, 93, 96, 99, 102, 105, 108, 111, 114, 117, 120, 123, 126] ∧
      (sampleOnlinePhases 2).totalTime = 897 ∧
      (sampleOnlinePhases 2).peakWorkspace = 126 := by
  decide

/-- A handler and table/advice hardwired into the retained main program are not separately
installed occurrences and therefore are not charged again under their independent categories. -/
def hardwiredStaticResources (n : ℕ) : Game.AttackResources :=
  ⟨[{ kind := .program, bits := 12 * n + 3 }], sampleExecution n⟩

theorem hardwiredStatic_not_doubleCounted (n : ℕ) :
    (hardwiredStaticResources n).adversaryBits = 0 ∧
      (hardwiredStaticResources n).reducerBits = 0 ∧
      (hardwiredStaticResources n).programBits = 12 * n + 3 ∧
      (hardwiredStaticResources n).handlerBits = 0 ∧
      (hardwiredStaticResources n).tableBits = 0 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A model-specific compiler certificate ties input/output lengths to the compiler and
compiler-output-copy ledger phases. -/
def SampleCompilerCertifies (n : ℕ)
    (resources : Game.ExecutedCompilerResources)
    (compilerPhase outputCopyPhase : Game.OnlinePhaseResources) : Prop :=
  resources.inputBits = 2 * n + 1 ∧
    resources.outputBits = 5 * n + 1 ∧
    compilerPhase.time = 18 * (n + 1) ∧
    compilerPhase.workspace = 31 * (n + 1) ∧
    outputCopyPhase.time = 19 * (n + 1) ∧
    outputCopyPhase.workspace = 32 * (n + 1) ∧
    resources.outputBits ≤ compilerPhase.time ∧
    resources.outputBits ≤ outputCopyPhase.time

/-- Separate compiler installation charges the compiler occurrence and emitted generated-program
occurrence, and connects every compiler coordinate to the model-specific certificate. -/
theorem sampleCompiler_accounted (n : ℕ) :
    Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
      (.separatelyInstalled (7 * n + 1)) (sampleResources n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Game.CompilerInstallation.IsInInventory, sampleResources, sampleInventory]
  · simp [sampleResources, sampleInventory, sampleExecution, sampleCompilerExecution]
  · simp only [SampleCompilerCertifies, sampleResources, sampleExecution,
      sampleCompilerExecution, sampleOnlinePhases, true_and]
    constructor <;> omega
  · change 18 * (n + 1) + 19 * (n + 1) ≤ 299 * n + 299
    omega
  · change 31 * (n + 1) ≤ 42 * n + 42
    omega
  · change 32 * (n + 1) ≤ 42 * n + 42
    omega

/-- The same executed compiler may be inlined into one installed main program. No separate
compiler occurrence is present or charged; the emitted program remains a distinct occurrence. -/
def inlinedCompilerResources (n : ℕ) : Game.AttackResources :=
  ⟨[{ kind := .program, bits := 12 * n + 2 },
    { kind := .generatedProgram, bits := 5 * n + 1 }], sampleExecution n⟩

theorem inlinedCompiler_accounted (n : ℕ) :
    (inlinedCompilerResources n).compilerBits = 0 ∧
      Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
        (.inlinedIntoProgram (12 * n + 2)) (inlinedCompilerResources n) := by
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Game.CompilerInstallation.IsInInventory, inlinedCompilerResources]
  · simp [inlinedCompilerResources, sampleExecution, sampleCompilerExecution]
  · simp only [SampleCompilerCertifies, inlinedCompilerResources, sampleExecution,
      sampleCompilerExecution, sampleOnlinePhases, true_and]
    constructor <;> omega
  · change 18 * (n + 1) + 19 * (n + 1) ≤ 299 * n + 299
    omega
  · change 31 * (n + 1) ≤ 42 * n + 42
    omega
  · change 32 * (n + 1) ≤ 42 * n + 42
    omega

/-- A model-specific whole-attack certificate connects initial input, emitted output, production
and output copying to the declared online execution. -/
def SampleAttackCertifies (n : ℕ)
    (resources : Game.AttackExecutionResources) : Prop :=
  resources.inputBits = 12 * n + 1 ∧
    resources.outputBits = 16 * n + 1 ∧
    resources.phases = sampleOnlinePhases n ∧
    resources.outputBits ≤ resources.phases.outputProduction.time ∧
    resources.outputBits ≤ resources.phases.outputCopy.time

/-- The model certificate covers every phase, and the declared online time and workspace are the
exact ledger sum and peak rather than additional charges. -/
theorem sampleOnlinePhases_accounted (n : ℕ) :
    Game.AttackResources.AccountsForOnlinePhases SampleAttackCertifies n
      (sampleResources n) := by
  refine ⟨?_, ?_, ?_⟩
  · simp only [SampleAttackCertifies, sampleResources, sampleExecution, sampleOnlinePhases,
      true_and]
    constructor <;> omega
  · change (sampleOnlinePhases n).totalTime = 299 * n + 299
    simp [Game.OnlinePhaseLedger.totalTime, Game.OnlinePhaseLedger.asList,
      sampleOnlinePhases]
    omega
  · change (sampleOnlinePhases n).peakWorkspace = 42 * n + 42
    simp [Game.OnlinePhaseLedger.peakWorkspace, Game.OnlinePhaseLedger.asList,
      sampleOnlinePhases]
    omega

theorem sampleOutput_accounted (n : ℕ) :
    Game.AttackResources.AccountsForOutput SampleAttackCertifies n (sampleResources n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [SampleAttackCertifies, sampleResources, sampleExecution, sampleOnlinePhases,
      true_and]
    constructor <;> omega
  · change 17 * (n + 1) + 28 * (n + 1) + 29 * (n + 1) ≤ 299 * n + 299
    omega
  · change 30 * (n + 1) ≤ 42 * n + 42
    omega
  · change 41 * (n + 1) ≤ 42 * n + 42
    omega
  · change 42 * (n + 1) ≤ 42 * n + 42
    omega

/-- Offline compilation contributes no compiler execution costs, while its generated program is
still a nonconstant installed occurrence and the attack's own output remains explicit. -/
def offlinePhases (n : ℕ) : Game.OnlinePhaseLedger where
  inputRead := { time := n, workspace := n + 1 }
  compiler := { time := 0, workspace := 0 }
  compilerOutputCopy := { time := 0, workspace := 0 }
  marshalling := { time := 0, workspace := 0 }
  tags := { time := 0, workspace := 0 }
  dispatch := { time := 0, workspace := 0 }
  queryRequest := { time := 0, workspace := 0 }
  queryReply := { time := 0, workspace := 0 }
  handler := { time := 0, workspace := 0 }
  interpreter := { time := 0, workspace := 0 }
  controller := { time := 0, workspace := 0 }
  outputProduction := { time := n + 1, workspace := n + 1 }
  outputCopy := { time := n + 1, workspace := n + 1 }

def offlineCompiledResources (n : ℕ) : Game.AttackResources :=
  ⟨[{ kind := .program, bits := 2 * n + 1 },
    { kind := .generatedProgram, bits := n + 1 }], {
    inputBits := n
    onlineTime := 3 * n + 2
    onlineWorkspace := n + 1
    phases := offlinePhases n
    compiler := { inputBits := 0, outputBits := 0 }
    randomBits := n
    classicalQueries := n
    quantumQueries := n
    qubits := n + 1
    gates := 2 * n + 1
    requestBits := n
    replyBits := n
    outputBits := n + 1 }⟩

theorem offlineCompilation_separate (n : ℕ) :
    (offlineCompiledResources n).programBits = 2 * n + 1 ∧
      (offlineCompiledResources n).generatedProgramBits = n + 1 ∧
      (offlineCompiledResources n).compilerBits = 0 ∧
      (offlineCompiledResources n).execution.compiler.inputBits = 0 ∧
      (offlineCompiledResources n).execution.compiler.outputBits = 0 ∧
      (offlineCompiledResources n).execution.phases.compiler.time = 0 ∧
      (offlineCompiledResources n).execution.phases.compiler.workspace = 0 ∧
      (offlineCompiledResources n).execution.phases.compilerOutputCopy.time = 0 ∧
      (offlineCompiledResources n).execution.phases.compilerOutputCopy.workspace = 0 := by
  simp [offlineCompiledResources, offlinePhases,
    Game.AttackResources.programBits, Game.AttackResources.generatedProgramBits,
    Game.AttackResources.compilerBits, Game.AttackResources.artifactBits,
    Game.InstalledArtifact.installedBits]

theorem offlinePhaseAggregates (n : ℕ) :
    (offlinePhases n).totalTime = 3 * n + 2 ∧
      (offlinePhases n).peakWorkspace = n + 1 := by
  constructor
  · simp [Game.OnlinePhaseLedger.totalTime, Game.OnlinePhaseLedger.asList, offlinePhases]
    omega
  · simp [Game.OnlinePhaseLedger.peakWorkspace, Game.OnlinePhaseLedger.asList, offlinePhases]

private theorem linearPhase_isPolynomial (timeCoeff workspaceCoeff : ℕ) :
    Game.OnlinePhaseResources.IsPolynomial
      (fun n => (⟨timeCoeff * (n + 1), workspaceCoeff * (n + 1)⟩ :
        Game.OnlinePhaseResources)) where
  time := by fun_prop
  workspace := by fun_prop

/-- Every named sample phase has independently polynomial time and workspace. -/
theorem sampleOnlinePhases_isPolynomial :
    Game.OnlinePhaseLedger.IsPolynomial sampleOnlinePhases where
  inputRead := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 17 30
  compiler := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 18 31
  compilerOutputCopy := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 19 32
  marshalling := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 20 33
  tags := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 21 34
  dispatch := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 22 35
  queryRequest := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 23 36
  queryReply := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 24 37
  handler := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 25 38
  interpreter := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 26 39
  controller := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 27 40
  outputProduction := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 28 41
  outputCopy := by
    simpa [sampleOnlinePhases] using linearPhase_isPolynomial 29 42

private theorem sampleArtifactBits_isPolynomial (kind : Game.InstalledArtifactKind) :
    PolynomiallyBounded fun n => (sampleResources n).artifactBits kind := by
  cases kind with
  | adversary =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => n + 1) by fun_prop)
  | reducer =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 2 * n + 1) by fun_prop)
  | program =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => (3 * n + 1) + (4 * n + 1)) by fun_prop)
  | generatedProgram =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 5 * n + 1) by fun_prop)
  | generator =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 6 * n + 1) by fun_prop)
  | compiler =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 7 * n + 1) by fun_prop)
  | interpreter =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 8 * n + 1) by fun_prop)
  | controller =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 9 * n + 1) by fun_prop)
  | handler =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 10 * n + 1) by fun_prop)
  | table =>
      simpa [sampleResources, sampleInventory,
        Game.AttackResources.artifactBits, Game.InstalledArtifact.installedBits] using
        (show PolynomiallyBounded (fun n => 11 * n + 1) by fun_prop)

/-- The sample family is componentwise polynomial; no scalar resource sum is used. -/
theorem sampleResources_isPolynomial :
    Game.AttackResources.IsPolynomial sampleResources where
  adversaryBits := by
    simpa only [Game.AttackResources.adversaryBits] using
      sampleArtifactBits_isPolynomial .adversary
  reducerBits := by
    simpa only [Game.AttackResources.reducerBits] using
      sampleArtifactBits_isPolynomial .reducer
  programBits := by
    simpa only [Game.AttackResources.programBits] using
      sampleArtifactBits_isPolynomial .program
  generatedProgramBits := by
    simpa only [Game.AttackResources.generatedProgramBits] using
      sampleArtifactBits_isPolynomial .generatedProgram
  generatorBits := by
    simpa only [Game.AttackResources.generatorBits] using
      sampleArtifactBits_isPolynomial .generator
  compilerBits := by
    simpa only [Game.AttackResources.compilerBits] using
      sampleArtifactBits_isPolynomial .compiler
  interpreterBits := by
    simpa only [Game.AttackResources.interpreterBits] using
      sampleArtifactBits_isPolynomial .interpreter
  controllerBits := by
    simpa only [Game.AttackResources.controllerBits] using
      sampleArtifactBits_isPolynomial .controller
  handlerBits := by
    simpa only [Game.AttackResources.handlerBits] using
      sampleArtifactBits_isPolynomial .handler
  tableBits := by
    simpa only [Game.AttackResources.tableBits] using
      sampleArtifactBits_isPolynomial .table
  inputBits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 12 * n + 1) by fun_prop)
  onlineTime := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 299 * n + 299) by fun_prop)
  onlineWorkspace := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 42 * n + 42) by fun_prop)
  phases := by
    simpa only [sampleResources, sampleExecution] using
      sampleOnlinePhases_isPolynomial
  compilerInputBits := by
    simpa only [sampleResources, sampleExecution, sampleCompilerExecution] using
      (show PolynomiallyBounded (fun n => 2 * n + 1) by fun_prop)
  compilerOutputBits := by
    simpa only [sampleResources, sampleExecution, sampleCompilerExecution] using
      (show PolynomiallyBounded (fun n => 5 * n + 1) by fun_prop)
  randomBits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 14 * n + 1) by fun_prop)
  classicalQueries := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 15 * n + 1) by fun_prop)
  quantumQueries := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 16 * n + 1) by fun_prop)
  qubits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 17 * n + 1) by fun_prop)
  gates := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 18 * n + 1) by fun_prop)
  requestBits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 19 * n + 1) by fun_prop)
  replyBits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 20 * n + 1) by fun_prop)
  outputBits := by
    simpa only [sampleResources, sampleExecution] using
      (show PolynomiallyBounded (fun n => 16 * n + 1) by fun_prop)

/-- The finite predicate records the exact profile and requires the model-specific compiler and
whole-execution certificates. It derives no existential program. -/
def WithinSample (n : ℕ) (budget : Game.AttackResources)
    (_adversary : ℕ → Bool) : Prop :=
  (sampleResources n).Fits budget ∧
    Game.AttackResources.AccountsForExecutedCompiler SampleCompilerCertifies n
      (.separatelyInstalled (7 * n + 1)) (sampleResources n) ∧
    Game.AttackResources.AccountsForOnlinePhases SampleAttackCertifies n
      (sampleResources n) ∧
    Game.AttackResources.AccountsForOutput SampleAttackCertifies n (sampleResources n)

/-- A deliberately neutral game family used to isolate the resource bridge. -/
noncomputable def sampleGame (adversary : ℕ → Bool) (n : ℕ) : Game :=
  PMF.pure (adversary n)

/-- Finite indistinguishability under the exact nonconstant componentwise profile. -/
theorem indistinguishableWithin_sampleGame :
    Game.IndistinguishableWithin sampleGame sampleGame WithinSample (fun _ _ => 0) :=
  Game.IndistinguishableWithin.refl sampleGame WithinSample

/-- The finite bound lifts along the supplied nonconstant polynomial schedule. -/
theorem indistinguishable_sampleGame :
    Game.Indistinguishable sampleGame sampleGame (fun _ => True) := by
  refine indistinguishableWithin_sampleGame.indistinguishable_attackResources ?_ ?_
  · intro adversary _
    exact ⟨sampleResources, sampleResources_isPolynomial, fun n => by
      exact ⟨Game.AttackResources.fits_refl (sampleResources n),
        sampleCompiler_accounted n, sampleOnlinePhases_accounted n,
        sampleOutput_accounted n⟩⟩
  · intro schedule _
    exact negligible_zero

end Cslib.Tests.AttackResources
