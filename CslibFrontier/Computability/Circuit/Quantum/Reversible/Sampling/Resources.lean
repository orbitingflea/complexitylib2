/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.EncodingSize
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Uniform
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling
import CslibFrontier.Computability.Circuit.Quantum.Reversible.Resources

/-!
# Concrete costs of reversible Boolean samplers

The exact sampler construction uses `n` Hadamard gates to prepare `n` fair seed bits, at most
three reversible gates per Boolean gate, and one CNOT per copied output. Its active register keeps
all `n` seeds and `G` Boolean gate values, one compiler zero qubit, and `m` copied outputs. The
description has no coherent oracle query and `samplerDist` performs one final measurement.

The finite sampler description records the exact active width, measures the full register before
the deterministic suffix readout, and has no quantum input or oracle registers. Its encoded length
therefore charges all register metadata and the mapped instruction list. The separate
instruction-list bound includes unary wire numbers and framing, but does not bound the static
generator program or its offline running time. Those are separate from the online gate and qubit
costs recorded here.

## Main definitions

* `Cslib.Quantum.Reversible.samplerDescription`: the complete finite circuit description used for
  resource accounting.

## Main results

* `Cslib.Quantum.Reversible.samplerWidth_circuit`: exact active width for a typed circuit.
* `Cslib.Quantum.Reversible.length_samplerCodes_le`: at most `n + 3 * G + m` gates.
* `Cslib.Quantum.Reversible.length_encoding_samplerCodes_le`: encoded instruction length.
* `Cslib.Quantum.Reversible.within_samplerCodes`: separate qubit, gate, zero-query, and exact
  encoded-description budgets.
-/

public section

namespace Cslib.Quantum.Reversible

open Circuits Circuits.Boolean GateCode Turing.MultiTapeTM

/-- The finite oracle-circuit view of the sampler. It starts with every qubit zero, performs no
oracle query, and measures the full register before `samplerReadout` selects the copied suffix. -/
def samplerDescription (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) : OracleCircuitDescription where
  width := samplerWidth n code
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := samplerWidth n code
  instructions := (samplerCodes n code).map fun g => OracleGateCode.gate (false, g)

/-- A typed circuit sampler retains every input and gate value, one fixed-zero qubit, and one
fresh qubit for every output. -/
theorem samplerWidth_circuit {n m : ℕ} (C : Circuits.Circuit signature n m) :
    samplerWidth n C.code = n + C.size + 1 + m := by
  unfold samplerWidth samplerOutputStart samplerZero
  rw [Circuit.length_code_fst]
  simp [Circuit.code]

/-- The complete sampler uses at most one Hadamard per seed, three reversible gates per Boolean
gate, and one CNOT per copied output. -/
theorem length_samplerCodes_le (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    (samplerCodes n code).length ≤ n + 3 * code.1.length + code.2.length := by
  have h := length_codes_le n (samplerZero n code) code.1
  rw [length_samplerCodes]
  omega

/-- The generated sampler's encoded instruction list, including framing and unary wire indices,
has the stated construction-derived bound. -/
theorem length_encoding_samplerCodes_le (n : ℕ)
    (code : List (Op × List ℕ) × List ℕ) :
    (encList encGateCode (samplerCodes n code)).length ≤
      (n + 3 * code.1.length + code.2.length) * (12 * samplerWidth n code + 1) :=
  (length_encGateCodes_le (wellFormed_samplerCodes n code)).trans
    (Nat.mul_le_mul_right _ (length_samplerCodes_le n code))

/-- The finite sampler description uses the exact active width, construction-derived gate budget,
no coherent oracle queries, and its full encoded length. -/
theorem within_samplerCodes (n : ℕ) (code : List (Op × List ℕ) × List ℕ) :
    OracleCircuit.Within ((samplerCodes n code).map fun g => OracleGateCode.gate (false, g))
      (samplerWidth n code)
      (encOracleCircuitDescription (samplerDescription n code)).length
      ⟨samplerWidth n code, n + 3 * code.1.length + code.2.length, 0,
        (encOracleCircuitDescription (samplerDescription n code)).length⟩ := by
  have hcounts :
      OracleCircuit.gateCount
          ((samplerCodes n code).map fun g => OracleGateCode.gate (false, g)) =
          (samplerCodes n code).length ∧
        OracleCircuit.queryCount
          ((samplerCodes n code).map fun g => OracleGateCode.gate (false, g)) = 0 := by
    simp [OracleCircuit.gateCount, OracleCircuit.queryCount, OracleGateCode.isQuery,
      List.countP_map, Function.comp_def]
  rw [OracleCircuit.Within, hcounts.1, hcounts.2]
  exact ⟨le_rfl, length_samplerCodes_le n code, le_rfl, le_rfl⟩

end Cslib.Quantum.Reversible
