/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests)

public import CslibFrontier.Computability.Circuit.Quantum.Input
public import CslibFrontier.Computability.Circuit.Quantum.PhaseCode.Relabel

public section

namespace Cslib.Quantum.Tests.PhaseCodeRelabel

def sparseEmbedding : Fin 2 ↪ Fin 4 :=
  ⟨![0, 2], by intro i j h; fin_cases i <;> fin_cases j <;> simp_all⟩

def sparseRelabel (i : ℕ) : ℕ := 2 * i

def codes : List PhaseGateCode :=
  [(true, false, 0, [1]), (false, false, 1, [0])]

theorem codes_wellFormed (c : PhaseGateCode) (hc : c ∈ codes) : c.WellFormed 2 := by
  simp only [codes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> decide

theorem sparseRelabel_agrees (i : Fin 2) :
    sparseRelabel i = (sparseEmbedding i : ℕ) := by
  fin_cases i <;> rfl

/-- A sparse relabelling of both a controlled phase gate and a CNOT acts on exactly the selected
qubits of the larger register. -/
theorem eval_sparseRelabel (x : Fin 4 → Bool) (ψ : Qubits 2) :
    Circuit.eval
        (Circuit.ofPhaseCodes 4 (codes.map (PhaseGateCode.relabel sparseRelabel)))
        (embedState sparseEmbedding x ψ) =
      embedState sparseEmbedding x (Circuit.eval (Circuit.ofPhaseCodes 2 codes) ψ) := by
  rw [Circuit.ofPhaseCodes_map_relabel sparseEmbedding sparseRelabel sparseRelabel_agrees
    codes_wellFormed]
  exact Circuit.eval_mapWires_embedState _ _ _ _

end Cslib.Quantum.Tests.PhaseCodeRelabel
