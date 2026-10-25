/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Quantum.Basic

/-! Quantum circuits: concrete runs, and objects that fail the definitions. -/

namespace ComplexityTests.QuantumCircuit

open Cslib.Quantum Matrix

/-- The Hadamard gate on the only qubit of a one-qubit register. -/
noncomputable def h₀ : PlacedGate 1 := ⟨1, Gate.hadamard, Function.Embedding.refl _⟩

-- `H|0⟩ = (|0⟩ + |1⟩)/√2`: measuring it gives each outcome with probability `1 / 2`.
example (y : Fin 1 → Bool) : Circuit.measure [h₀] (fun _ => false) y = 1 / 2 := by
  simp only [Circuit.measure, measure_apply, Circuit.run, Circuit.eval_cons, Circuit.eval_nil,
    PlacedGate.eval_ket_apply, PlacedGate.matrix_apply, h₀, Function.Embedding.refl_apply,
    exists_eq, not_true_eq_false, IsEmpty.forall_iff, implies_true, ite_true, Gate.hadamard_apply]
  simp

-- Interference: `HH = I`, so after two Hadamard gates qubit `0` never reads `1`, although after
-- one it reads `1` with probability `1 / 2`.
example (x : Fin 1 → Bool) : Circuit.run [h₀, h₀] x = ket x := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval, ← unitaryEquiv_mul,
    PlacedGate.matrix, h₀, ← map_mul, Gate.hadamard_mul_self, map_one, unitaryEquiv_one]

example : measureProb (Circuit.run [h₀, h₀] (fun _ => false)) {fun _ => true} = 0 := by
  have : Circuit.run [h₀, h₀] (fun _ => false) = ket fun _ => false := by
    simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, PlacedGate.eval,
      ← unitaryEquiv_mul, PlacedGate.matrix, h₀, ← map_mul, Gate.hadamard_mul_self, map_one,
      unitaryEquiv_one]
  have hne : (fun _ : Fin 1 => true) ≠ fun _ => false := fun h => by simpa using congrFun h 0
  simp [this, measureProb, hne]

/-- The NOT gate on the only qubit of a one-qubit register. -/
noncomputable def x₀ : PlacedGate 1 := ⟨1, Gate.not, Function.Embedding.refl _⟩

-- Gates act first to last: `run [X, H] |0⟩ = H X |0⟩ = H |1⟩ = (|0⟩ - |1⟩)/√2`, whose amplitude on
-- `|1⟩` is `-1/√2`; in the other order, `X H |0⟩ = (|0⟩ + |1⟩)/√2` would give `+1/√2`.
example : (Circuit.run [x₀, h₀] fun _ => false).ofLp (fun _ => true) =
    -((Real.sqrt 2)⁻¹ : ℝ) := by
  have hx : x₀.eval (ket fun _ => false) = ket fun _ => true := by
    simp only [x₀, Gate.not, Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
    congr 1
    funext j
    exact (splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ j).trans (by
      fin_cases j; rfl)
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, hx, PlacedGate.eval_ket_apply,
    PlacedGate.matrix_apply, h₀, Function.Embedding.refl_apply, exists_eq, not_true_eq_false,
    IsEmpty.forall_iff, implies_true, ite_true, Gate.hadamard_apply]
  simp

/-- The Toffoli gate on the three qubits of a three-qubit register, in order. -/
noncomputable def toffoli₀ : PlacedGate 3 := ⟨3, Gate.toffoli, Function.Embedding.refl _⟩

-- Toffoli flips the target when both controls are set: `|110⟩ ↦ |111⟩`.
example : Circuit.run [toffoli₀] ![true, true, false] = ket ![true, true, true] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, toffoli₀, Gate.toffoli,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  exact (splitEquiv_symm_apply_wire (Function.Embedding.refl _) _ _ j).trans (by
    fin_cases j <;> rfl)

/-- CNOT with control qubit `2` and target qubit `0` of a three-qubit register. -/
noncomputable def cnot₂₀ : PlacedGate 3 := ⟨2, Gate.cnot, ⟨![2, 0], by decide⟩⟩

-- The wires are ordered: qubit `2` controls qubit `0`, and qubit `1` is untouched, so
-- `|001⟩ ↦ |101⟩` and `|110⟩` is fixed.
example : Circuit.run [cnot₂₀] ![false, false, true] = ket ![true, false, true] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, cnot₂₀, Gate.cnot,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  fin_cases j
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 1
  · exact (splitEquiv_symm_apply_of_not ⟨![2, 0], _⟩ _ _ 1 (by decide)).trans rfl
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 0

example : Circuit.run [cnot₂₀] ![true, true, false] = ket ![true, true, false] := by
  simp only [Circuit.run, Circuit.eval_cons, Circuit.eval_nil, cnot₂₀, Gate.cnot,
    Gate.ofInvolutive, PlacedGate.eval_ofPerm_ket]
  congr 1
  funext j
  fin_cases j
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 1
  · exact (splitEquiv_symm_apply_of_not ⟨![2, 0], _⟩ _ _ 1 (by decide)).trans rfl
  · exact splitEquiv_symm_apply_wire ⟨![2, 0], _⟩ _ _ 0

-- The circuit `H; Toffoli` is over the gate set `{H, Toffoli}`, but a circuit containing `H` is
-- not over `{Toffoli}`.
example : Circuit.IsOver {⟨1, Gate.hadamard⟩, ⟨3, Gate.toffoli⟩}
    [(⟨1, Gate.hadamard, ⟨![0], by decide⟩⟩ : PlacedGate 3), toffoli₀] := by
  simp [Circuit.IsOver, toffoli₀]

example : ¬Circuit.IsOver {⟨3, Gate.toffoli⟩} [h₀] := fun h =>
  absurd (congrArg Sigma.fst (h h₀ List.mem_cons_self)) (by decide)

-- A non-unitary matrix is not a gate: `[[1, 1], [0, 1]]` is not unitary.
example : !![(1 : ℂ), 1; 0, 1] ∉ unitaryGroup (Fin 2) ℂ := by
  intro h
  have := congrFun (congrFun (mem_unitaryGroup_iff.mp h) 0) 0
  simp [mul_apply, Fin.sum_univ_two, star_eq_conjTranspose] at this

-- A two-qubit gate cannot be placed on a one-qubit register: the wires must be distinct.
example : IsEmpty (Fin 2 ↪ Fin 1) :=
  ⟨fun f => absurd (f.injective (Subsingleton.elim (f 0) (f 1))) (by decide)⟩

end ComplexityTests.QuantumCircuit
