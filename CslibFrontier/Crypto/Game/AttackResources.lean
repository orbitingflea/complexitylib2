/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.Concrete

/-!
# Componentwise resources for concrete security

Concrete reductions need to retain static descriptions and charge online execution without
identifying unrelated units. An explicit `InstalledArtifact` list records each stored occurrence.
Per-kind description sizes are sums over that inventory, so distinct stored copies contribute
separately, while components inlined into a final artifact are not charged again. Adversaries,
reducers and generic or main programs have independent coordinates; separately installed handlers
and static tables or advice use their own occurrences too. `AttackResources` adds the common
execution coordinates; `Fits` and `IsPolynomial` keep every comparison and asymptotic bound
componentwise.

Offline generation is not online time unless the attack executes it. A generated artifact is still
an installed occurrence, whether its compiler ran online or offline. A canonical phase ledger
records input reading, compilation and its output copy, marshalling, tags, dispatch, request/reply
handling, handler/interpreter/controller work, and final-output production and copying. Its time sum
and peak workspace are certified against the aggregate online coordinates. Compiler and final-
output accounting refer to ledger phases rather than adding duplicate time or workspace fields.

This module sums only the times of the named online phases and takes their workspace maximum. It
supplies no scalar total across unrelated units; any further aggregation must state its units and
be proved separately. It also supplies no program, circuit or controller: callers provide exact
retained artifacts and prove that their executions fit the declared budget.

## Main definitions

* `Cslib.Crypto.Game.InstalledArtifactKind`: roles for independently retained static artifacts.
* `Cslib.Crypto.Game.InstalledArtifact`: one occurrence in the installed static inventory.
* `Cslib.Crypto.Game.OnlinePhaseLedger`: named online phases with exact aggregate operations.
* `Cslib.Crypto.Game.ExecutedCompilerResources`: executed compiler input and output lengths.
* `Cslib.Crypto.Game.AttackExecutionResources`: online, compiler, oracle and communication costs.
* `Cslib.Crypto.Game.AttackResources`: installed inventory plus execution resources.
* `Cslib.Crypto.Game.CompilerInstallation`: separate or inlined representation of compiler logic.
* `Cslib.Crypto.Game.AttackResources.Fits`: componentwise finite-budget comparison.
* `Cslib.Crypto.Game.AttackResources.AccountsForExecutedCompiler`: an online compiler and its
  emitted installed program are certified and charged without duplicating inlined code.
* `Cslib.Crypto.Game.AttackResources.AccountsForOnlinePhases`: a model certificate connects the
  ledger to execution and its exact time/workspace aggregates.
* `Cslib.Crypto.Game.AttackResources.AccountsForOutput`: initial input, emitted output and copying
  are connected to a model-specific execution certificate.
* `Cslib.Crypto.Game.AttackResources.IsPolynomial`: componentwise polynomial resource families.

## Main results

* `Cslib.Crypto.Game.IndistinguishableWithin.indistinguishable_attackResources`: specialize the
  existing finite-to-asymptotic bridge to componentwise attack resources.

## References

This resource interface and bridge are original infrastructure.
-/

public section

namespace Cslib.Crypto.Game

open scoped NNReal

/-- The role of one separately installed static artifact occurrence. A final program containing
hardwired components is one `program` occurrence; those components are not additional occurrences.
-/
inductive InstalledArtifactKind
  /-- A retained adversary program or circuit description. -/
  | adversary
  /-- A retained reduction program or circuit description. -/
  | reducer
  /-- A retained generic or main program or circuit description. -/
  | program
  /-- A retained program or circuit emitted by a compiler. -/
  | generatedProgram
  /-- A retained uniform generator description. -/
  | generator
  /-- A retained compiler description. -/
  | compiler
  /-- A retained universal interpreter description. -/
  | interpreter
  /-- A separately retained wrapper or controller description. -/
  | controller
  /-- A separately retained oracle, query or operation-handler description. -/
  | handler
  /-- A separately retained transition, dispatch or lookup table, including static advice. -/
  | table
  deriving DecidableEq

/-- One occurrence in the installed static inventory. Repeating the same value in the inventory
models distinct stored copies and charges each copy once. -/
structure InstalledArtifact where
  /-- The role under which this occurrence is installed. -/
  kind : InstalledArtifactKind
  /-- Exact encoded length of this occurrence. -/
  bits : ℕ
  deriving DecidableEq

namespace InstalledArtifact

/-- Description bits of the occurrences of `kind` in an explicit installed inventory. -/
@[expose] def installedBits : List InstalledArtifact → InstalledArtifactKind → ℕ
  | [], _ => 0
  | artifact :: inventory, kind =>
      (if artifact.kind = kind then artifact.bits else 0) + installedBits inventory kind

/-- Concatenating inventories adds their per-kind occurrence sums. In particular, separately
stored copies appearing in both inventories are charged separately. -/
theorem installedBits_append (first second : List InstalledArtifact)
    (kind : InstalledArtifactKind) :
    installedBits (first ++ second) kind =
      installedBits first kind + installedBits second kind := by
  induction first with
  | nil => simp [installedBits]
  | cons artifact first ih =>
      simp only [List.cons_append, installedBits, ih, Nat.add_assoc]

end InstalledArtifact

/-- Time and peak workspace charged to one named online phase. -/
structure OnlinePhaseResources where
  /-- Steps executed in this phase. -/
  time : ℕ
  /-- Peak workspace used during this phase. -/
  workspace : ℕ
  deriving DecidableEq

namespace OnlinePhaseResources

/-- Componentwise comparison of one online phase. -/
@[expose] def Fits (used budget : OnlinePhaseResources) : Prop :=
  used.time ≤ budget.time ∧ used.workspace ≤ budget.workspace

instance (used budget : OnlinePhaseResources) : Decidable (used.Fits budget) := by
  unfold Fits
  infer_instance

/-- A phase schedule has independently polynomial time and workspace. -/
structure IsPolynomial (schedule : ℕ → OnlinePhaseResources) : Prop where
  time : PolynomiallyBounded fun n => (schedule n).time
  workspace : PolynomiallyBounded fun n => (schedule n).workspace

end OnlinePhaseResources

/-- Canonical ledger of online phases. Sequential phase times add; workspace is aggregated by
maximum because phases need not retain each other's temporary storage. Compiler and output-copy
costs occur here only, rather than in duplicate view fields. -/
structure OnlinePhaseLedger where
  /-- Reading and decoding the attack's initial input. -/
  inputRead : OnlinePhaseResources
  /-- Executing an online compiler, including production of its emitted description. -/
  compiler : OnlinePhaseResources
  /-- Retaining or copying the compiler's emitted description. -/
  compilerOutputCopy : OnlinePhaseResources
  /-- Marshalling values between representations. -/
  marshalling : OnlinePhaseResources
  /-- Producing, checking or routing tags. -/
  tags : OnlinePhaseResources
  /-- Dispatching operations or oracle calls. -/
  dispatch : OnlinePhaseResources
  /-- Producing and transferring query requests. -/
  queryRequest : OnlinePhaseResources
  /-- Receiving and decoding query replies. -/
  queryReply : OnlinePhaseResources
  /-- Executing separately identified handler logic. -/
  handler : OnlinePhaseResources
  /-- Executing interpreter logic. -/
  interpreter : OnlinePhaseResources
  /-- Executing wrapper or controller logic. -/
  controller : OnlinePhaseResources
  /-- Producing the attack's final encoded output. -/
  outputProduction : OnlinePhaseResources
  /-- Retaining or copying the final encoded output. -/
  outputCopy : OnlinePhaseResources
  deriving DecidableEq

namespace OnlinePhaseLedger

/-- The canonical phase order used for aggregation. -/
@[expose] def asList (ledger : OnlinePhaseLedger) : List OnlinePhaseResources :=
  [ledger.inputRead, ledger.compiler, ledger.compilerOutputCopy, ledger.marshalling,
    ledger.tags, ledger.dispatch, ledger.queryRequest, ledger.queryReply, ledger.handler,
    ledger.interpreter, ledger.controller, ledger.outputProduction, ledger.outputCopy]

/-- Exact total online time: every named phase occurrence contributes once. -/
@[expose] def totalTime (ledger : OnlinePhaseLedger) : ℕ :=
  (ledger.asList.map fun phase => phase.time).sum

/-- Exact peak online workspace: the maximum of the named phase peaks. -/
@[expose] def peakWorkspace (ledger : OnlinePhaseLedger) : ℕ :=
  (ledger.asList.map fun phase => phase.workspace).foldl max 0

/-- Every phase coordinate of `used` fits the corresponding phase coordinate of `budget`. -/
@[expose] def Fits (used budget : OnlinePhaseLedger) : Prop :=
  used.inputRead.Fits budget.inputRead ∧
    used.compiler.Fits budget.compiler ∧
    used.compilerOutputCopy.Fits budget.compilerOutputCopy ∧
    used.marshalling.Fits budget.marshalling ∧
    used.tags.Fits budget.tags ∧
    used.dispatch.Fits budget.dispatch ∧
    used.queryRequest.Fits budget.queryRequest ∧
    used.queryReply.Fits budget.queryReply ∧
    used.handler.Fits budget.handler ∧
    used.interpreter.Fits budget.interpreter ∧
    used.controller.Fits budget.controller ∧
    used.outputProduction.Fits budget.outputProduction ∧
    used.outputCopy.Fits budget.outputCopy

instance (used budget : OnlinePhaseLedger) : Decidable (used.Fits budget) := by
  unfold Fits OnlinePhaseResources.Fits
  infer_instance

/-- A phase ledger is polynomial when every named phase coordinate is polynomial independently. -/
structure IsPolynomial (schedule : ℕ → OnlinePhaseLedger) : Prop where
  inputRead : OnlinePhaseResources.IsPolynomial fun n => (schedule n).inputRead
  compiler : OnlinePhaseResources.IsPolynomial fun n => (schedule n).compiler
  compilerOutputCopy :
    OnlinePhaseResources.IsPolynomial fun n => (schedule n).compilerOutputCopy
  marshalling : OnlinePhaseResources.IsPolynomial fun n => (schedule n).marshalling
  tags : OnlinePhaseResources.IsPolynomial fun n => (schedule n).tags
  dispatch : OnlinePhaseResources.IsPolynomial fun n => (schedule n).dispatch
  queryRequest : OnlinePhaseResources.IsPolynomial fun n => (schedule n).queryRequest
  queryReply : OnlinePhaseResources.IsPolynomial fun n => (schedule n).queryReply
  handler : OnlinePhaseResources.IsPolynomial fun n => (schedule n).handler
  interpreter : OnlinePhaseResources.IsPolynomial fun n => (schedule n).interpreter
  controller : OnlinePhaseResources.IsPolynomial fun n => (schedule n).controller
  outputProduction :
    OnlinePhaseResources.IsPolynomial fun n => (schedule n).outputProduction
  outputCopy : OnlinePhaseResources.IsPolynomial fun n => (schedule n).outputCopy

end OnlinePhaseLedger

/-- Input/output lengths of a compiler executed inside the attack experiment. Its execution and
output-copy costs are the corresponding online ledger phases, so they cannot be charged twice. -/
structure ExecutedCompilerResources where
  /-- Encoded compiler-input length, independent of the attack's initial input. -/
  inputBits : ℕ
  /-- Encoded length emitted by the compiler. -/
  outputBits : ℕ
  deriving DecidableEq

/-- Execution resources of an explicitly realized attack. Compiler coordinates are zero when
compilation is offline. Model-specific execution certificates separately justify that the declared
input/output lengths and step/workspace bounds describe the actual programs. -/
structure AttackExecutionResources where
  /-- Encoded length of the attack's initial input, distinct from oracle requests. -/
  inputBits : ℕ
  /-- Online steps, including marshalling, tags, dispatch, queries, interpreter/controller work,
  compiler work, and output production/copying, but excluding offline generation. -/
  onlineTime : ℕ
  /-- Peak online workspace, rather than the sum of workspace across sequential phases. -/
  onlineWorkspace : ℕ
  /-- Named online phase costs whose sum and maximum are certified against the aggregates above. -/
  phases : OnlinePhaseLedger
  /-- Executed compiler input/output lengths; both are zero when compilation is offline. -/
  compiler : ExecutedCompilerResources
  /-- Fair random bits consumed online. -/
  randomBits : ℕ
  /-- Classical oracle calls. -/
  classicalQueries : ℕ
  /-- Coherent quantum-oracle calls. -/
  quantumQueries : ℕ
  /-- Maximum simultaneously active qubits, including inputs and ancillas. -/
  qubits : ℕ
  /-- Executed elementary quantum gates. -/
  gates : ℕ
  /-- Maximum encoded request length. -/
  requestBits : ℕ
  /-- Maximum encoded reply length read by the attack. -/
  replyBits : ℕ
  /-- Maximum encoded output length emitted by the attack. -/
  outputBits : ℕ
  deriving DecidableEq

/-- Independent resources of an explicitly retained and executed attack. Static description sizes
are derived from the occurrence inventory rather than supplied as unaudited numeric labels. -/
structure AttackResources where
  /-- Every separately retained static occurrence, charged once. -/
  installedArtifacts : List InstalledArtifact
  /-- Online, compiler, oracle and communication coordinates. -/
  execution : AttackExecutionResources
  deriving DecidableEq

/-- How compiler logic used online is represented in the installed inventory. A separate compiler
is its own occurrence; an inlined compiler is part of one retained main-program occurrence and is
not also charged under `compiler`. The payload is that occurrence's exact encoded length. -/
inductive CompilerInstallation
  | separatelyInstalled (bits : ℕ)
  | inlinedIntoProgram (bits : ℕ)
  deriving DecidableEq

namespace CompilerInstallation

/-- The installed occurrence selected by a compiler-installation mode. -/
@[expose] def IsInInventory (installation : CompilerInstallation)
    (inventory : List InstalledArtifact) : Prop :=
  match installation with
  | .separatelyInstalled bits => { kind := .compiler, bits := bits } ∈ inventory
  | .inlinedIntoProgram bits => { kind := .program, bits := bits } ∈ inventory

instance (installation : CompilerInstallation) (inventory : List InstalledArtifact) :
    Decidable (installation.IsInInventory inventory) := by
  cases installation <;> unfold IsInInventory <;> infer_instance

end CompilerInstallation

namespace AttackResources

/-- Per-kind installed description bits of a resource profile. -/
@[expose] def artifactBits (resources : AttackResources)
    (kind : InstalledArtifactKind) : ℕ :=
  InstalledArtifact.installedBits resources.installedArtifacts kind

/-- Installed adversary-program or circuit bits, summed once per retained occurrence. -/
@[expose] def adversaryBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .adversary

/-- Installed reduction-program or circuit bits, summed once per retained occurrence. -/
@[expose] def reducerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .reducer

/-- Installed generic or main-program bits, summed once per retained occurrence. -/
@[expose] def programBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .program

/-- Installed compiler-emitted program or circuit bits, summed once per retained occurrence. -/
@[expose] def generatedProgramBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .generatedProgram

/-- Installed generator bits, summed once per retained occurrence. -/
@[expose] def generatorBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .generator

/-- Installed compiler bits, summed once per retained occurrence. -/
@[expose] def compilerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .compiler

/-- Installed interpreter bits, summed once per retained occurrence. -/
@[expose] def interpreterBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .interpreter

/-- Installed separately retained wrapper/controller bits, summed once per occurrence. -/
@[expose] def controllerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .controller

/-- Installed separately retained handler bits, summed once per occurrence. A handler hardwired
into the main program contributes only to `programBits`. -/
@[expose] def handlerBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .handler

/-- Installed separately retained transition, dispatch, lookup-table or static-advice bits,
summed once per occurrence. A table or advice string hardwired into the main program contributes
only to `programBits`. -/
@[expose] def tableBits (resources : AttackResources) : ℕ :=
  resources.artifactBits .table

/-- A model-specific certificate ties every named phase to the represented execution, while the
two equalities require exact aggregation rather than loose independent upper bounds. Compiler and
output views are not added here because their costs already occur in the ledger. -/
@[expose] def AccountsForOnlinePhases {Certificate : Type*}
    (Certifies : Certificate → AttackExecutionResources → Prop)
    (certificate : Certificate) (resources : AttackResources) : Prop :=
  Certifies certificate resources.execution ∧
    resources.execution.phases.totalTime = resources.execution.onlineTime ∧
    resources.execution.phases.peakWorkspace = resources.execution.onlineWorkspace

/-- An executed compiler is fully accounted for relative to a model-specific execution
certificate. The certificate connects compiler input/output and the ledger's compiler and
compiler-output-copy phases to an actual execution. The installation mode charges either a
separate compiler or the single main program containing inlined compiler logic. The emitted
description is a distinct `generatedProgram` occurrence. Phase costs are bounded by, but never
added again to, the overall online aggregates. -/
@[expose] def AccountsForExecutedCompiler {Certificate : Type*}
    (Certifies : Certificate → ExecutedCompilerResources →
      OnlinePhaseResources → OnlinePhaseResources → Prop)
    (certificate : Certificate) (installation : CompilerInstallation)
    (resources : AttackResources) : Prop :=
  installation.IsInInventory resources.installedArtifacts ∧
    { kind := .generatedProgram, bits := resources.execution.compiler.outputBits } ∈
      resources.installedArtifacts ∧
    Certifies certificate resources.execution.compiler resources.execution.phases.compiler
      resources.execution.phases.compilerOutputCopy ∧
    resources.execution.phases.compiler.time +
        resources.execution.phases.compilerOutputCopy.time ≤
      resources.execution.onlineTime ∧
    resources.execution.phases.compiler.workspace ≤ resources.execution.onlineWorkspace ∧
    resources.execution.phases.compilerOutputCopy.workspace ≤
      resources.execution.onlineWorkspace

/-- The attack's initial input, emitted output and copying are accounted for relative to a
model-specific execution certificate. This proposition is intended as an explicit part of a
concrete `Within` certificate; it does not manufacture an execution witness. -/
@[expose] def AccountsForOutput {Certificate : Type*}
    (Certifies : Certificate → AttackExecutionResources → Prop)
    (certificate : Certificate) (resources : AttackResources) : Prop :=
  Certifies certificate resources.execution ∧
    resources.execution.phases.inputRead.time +
        resources.execution.phases.outputProduction.time +
        resources.execution.phases.outputCopy.time ≤ resources.execution.onlineTime ∧
    resources.execution.phases.inputRead.workspace ≤ resources.execution.onlineWorkspace ∧
    resources.execution.phases.outputProduction.workspace ≤
      resources.execution.onlineWorkspace ∧
    resources.execution.phases.outputCopy.workspace ≤ resources.execution.onlineWorkspace

/-- `used` fits `budget` when every named coordinate fits independently. This intentionally does
not turn the coordinates into a scalar total. -/
@[expose] def Fits (used budget : AttackResources) : Prop :=
  used.adversaryBits ≤ budget.adversaryBits ∧
    used.reducerBits ≤ budget.reducerBits ∧
    used.programBits ≤ budget.programBits ∧
    used.generatedProgramBits ≤ budget.generatedProgramBits ∧
    used.generatorBits ≤ budget.generatorBits ∧
    used.compilerBits ≤ budget.compilerBits ∧
    used.interpreterBits ≤ budget.interpreterBits ∧
    used.controllerBits ≤ budget.controllerBits ∧
    used.handlerBits ≤ budget.handlerBits ∧
    used.tableBits ≤ budget.tableBits ∧
    used.execution.inputBits ≤ budget.execution.inputBits ∧
    used.execution.onlineTime ≤ budget.execution.onlineTime ∧
    used.execution.onlineWorkspace ≤ budget.execution.onlineWorkspace ∧
    used.execution.phases.Fits budget.execution.phases ∧
    used.execution.compiler.inputBits ≤ budget.execution.compiler.inputBits ∧
    used.execution.compiler.outputBits ≤ budget.execution.compiler.outputBits ∧
    used.execution.randomBits ≤ budget.execution.randomBits ∧
    used.execution.classicalQueries ≤ budget.execution.classicalQueries ∧
    used.execution.quantumQueries ≤ budget.execution.quantumQueries ∧
    used.execution.qubits ≤ budget.execution.qubits ∧
    used.execution.gates ≤ budget.execution.gates ∧
    used.execution.requestBits ≤ budget.execution.requestBits ∧
    used.execution.replyBits ≤ budget.execution.replyBits ∧
    used.execution.outputBits ≤ budget.execution.outputBits

instance (used budget : AttackResources) : Decidable (used.Fits budget) := by
  unfold Fits
  infer_instance

/-- Every exact resource profile fits itself. -/
theorem fits_refl (r : AttackResources) : r.Fits r := by
  simp [Fits, OnlinePhaseLedger.Fits, OnlinePhaseResources.Fits]

/-- A resource schedule is polynomial when each coordinate is polynomially bounded independently. -/
structure IsPolynomial (schedule : ℕ → AttackResources) : Prop where
  adversaryBits : PolynomiallyBounded fun n => (schedule n).adversaryBits
  reducerBits : PolynomiallyBounded fun n => (schedule n).reducerBits
  programBits : PolynomiallyBounded fun n => (schedule n).programBits
  generatedProgramBits : PolynomiallyBounded fun n => (schedule n).generatedProgramBits
  generatorBits : PolynomiallyBounded fun n => (schedule n).generatorBits
  compilerBits : PolynomiallyBounded fun n => (schedule n).compilerBits
  interpreterBits : PolynomiallyBounded fun n => (schedule n).interpreterBits
  controllerBits : PolynomiallyBounded fun n => (schedule n).controllerBits
  handlerBits : PolynomiallyBounded fun n => (schedule n).handlerBits
  tableBits : PolynomiallyBounded fun n => (schedule n).tableBits
  inputBits : PolynomiallyBounded fun n => (schedule n).execution.inputBits
  onlineTime : PolynomiallyBounded fun n => (schedule n).execution.onlineTime
  onlineWorkspace : PolynomiallyBounded fun n => (schedule n).execution.onlineWorkspace
  phases : OnlinePhaseLedger.IsPolynomial fun n => (schedule n).execution.phases
  compilerInputBits : PolynomiallyBounded fun n => (schedule n).execution.compiler.inputBits
  compilerOutputBits : PolynomiallyBounded fun n => (schedule n).execution.compiler.outputBits
  randomBits : PolynomiallyBounded fun n => (schedule n).execution.randomBits
  classicalQueries : PolynomiallyBounded fun n => (schedule n).execution.classicalQueries
  quantumQueries : PolynomiallyBounded fun n => (schedule n).execution.quantumQueries
  qubits : PolynomiallyBounded fun n => (schedule n).execution.qubits
  gates : PolynomiallyBounded fun n => (schedule n).execution.gates
  requestBits : PolynomiallyBounded fun n => (schedule n).execution.requestBits
  replyBits : PolynomiallyBounded fun n => (schedule n).execution.replyBits
  outputBits : PolynomiallyBounded fun n => (schedule n).execution.outputBits

end AttackResources

namespace IndistinguishableWithin

/-- Exact finite advantage bounds yield asymptotic indistinguishability when every admissible
adversary supplies an explicit componentwise-polynomial resource schedule and the finite error is
negligible along every such schedule. The schedule premise does not extract any program or circuit
from an existential efficiency hypothesis. -/
theorem indistinguishable_attackResources {Adversary : Type*}
    {game1 game2 : Adversary → ℕ → Game}
    {Within : ℕ → AttackResources → Adversary → Prop}
    {ε : ℕ → AttackResources → ℝ≥0}
    {Admissible : Adversary → Prop}
    (h : IndistinguishableWithin game1 game2 Within ε)
    (hsched : ∀ adversary, Admissible adversary →
      ∃ r : ℕ → AttackResources,
        AttackResources.IsPolynomial r ∧ ∀ n, Within n (r n) adversary)
    (hneg : ∀ r : ℕ → AttackResources, AttackResources.IsPolynomial r →
      Negligible (fun n => ε n (r n))) :
    Indistinguishable game1 game2 Admissible :=
  h.indistinguishable AttackResources.IsPolynomial hsched hneg

end IndistinguishableWithin

end Cslib.Crypto.Game
