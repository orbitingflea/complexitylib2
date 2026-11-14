/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler
public import CslibFrontier.Probability.PMF.Uniform

/-!
# Finite random oracles for native quantum executions

`Quantum.RandomOracle.sample` draws one complete finite Boolean table outside an experiment.
`Quantum.RandomOracle.runWith` specializes this operation to an existing native quantum
controller: the coherent device handler and the classical service factory receive the same table
for the complete adaptive run.

The coherent operation is the existing XOR oracle unitary
`|x, y⟩ ↦ |x, y + H(x)⟩`. These definitions only package finite eager-table semantics around that
operation. Drawing the table is not asserted to be efficient and is not charged to the native
controller. The controller's elementary-gate, coherent-query, measurement and classical-service
costs remain the separate existing resources.

This module does not establish a lazy/coherent equivalence, an unbounded or variable-length
random oracle, reprogramming, extraction, one-way-to-hiding, query depth, gate approximation,
equivalence with arbitrary QPPT adversaries or a protocol security theorem.

## Main definitions

* `Cslib.Quantum.RandomOracle.sample`: sample one table outside a finite experiment.
* `Cslib.Quantum.RandomOracle.runWith`: run one native controller with shared coherent and
  classical access to the sampled table.

## Main results

* `Cslib.Quantum.RandomOracle.sample_eq`: the sampler is exactly one outer uniform table draw.
* `Cslib.Quantum.RandomOracle.sample_const`: an experiment that does not inspect the table is
  unchanged.
* `Cslib.Quantum.RandomOracle.runWith_eq`: the controller wrapper is exactly one outer table draw
  followed by the existing fixed-table execution.

## References

* [R. de Wolf, *Quantum Computing: Lecture Notes*][deWolf2019], Section 15.1, p. 128.
-/

public section

namespace Cslib.Quantum.RandomOracle

/-- Draw one complete table before running the supplied finite experiment. Every use made by
`experiment` therefore sees the same table. This is ideal semantics, not an efficient sampler. -/
noncomputable def sample {a b : ℕ} {α : Type}
    (experiment : ((Fin a → Bool) → Fin b → Bool) → PMF α) : PMF α :=
  (Cslib.Probability.PMF.uniformOfFintype
    ((Fin a → Bool) → Fin b → Bool)).bind experiment

/-- The finite sampler is exactly one outer uniform-table bind. -/
theorem sample_eq {a b : ℕ} {α : Type}
    (experiment : ((Fin a → Bool) → Fin b → Bool) → PMF α) :
    sample experiment =
      (Cslib.Probability.PMF.uniformOfFintype
        ((Fin a → Bool) → Fin b → Bool)).bind experiment := by
  rfl

/-- Sampling is observationally irrelevant when an experiment never inspects the table. -/
@[simp] theorem sample_const {a b : ℕ} {α : Type} (p : PMF α) :
    sample (a := a) (b := b) (fun _ => p) = p := by
  exact PMF.bind_const _ _

variable {a b m r : ℕ} {κ State Operation α : Type}
  [Fintype κ] [DecidableEq κ]

/-- Sample one finite oracle, then execute the existing native controller. The service factory
receives the same `H` as `deviceWordHandler`, so coherent and classical calls cannot redraw it
inside this wrapper. -/
noncomputable def runWith
    (service : ((Fin a → Bool) → Fin b → Bool) →
      Operation × List Bool → StateT State PMF (Fin r → Bool))
    (program : ProbOracleComp
      (fun _ : (DeviceOperation ⊕ Operation) × List Bool => List Bool) α)
    (initial : DeviceState m κ State) : PMF (α × DeviceState m κ State) :=
  sample fun H => ProbOracleComp.runWith (deviceWordHandler H (service H)) program initial

/-- The sampled controller is exactly an outer uniform table draw followed by the existing
fixed-table execution. In particular, the service closure and every coherent query share `H`. -/
theorem runWith_eq
    (service : ((Fin a → Bool) → Fin b → Bool) →
      Operation × List Bool → StateT State PMF (Fin r → Bool))
    (program : ProbOracleComp
      (fun _ : (DeviceOperation ⊕ Operation) × List Bool => List Bool) α)
    (initial : DeviceState m κ State) :
    runWith service program initial =
      (Cslib.Probability.PMF.uniformOfFintype
        ((Fin a → Bool) → Fin b → Bool)).bind fun H =>
        ProbOracleComp.runWith (deviceWordHandler H (service H)) program initial := by
  rfl

end Cslib.Quantum.RandomOracle
