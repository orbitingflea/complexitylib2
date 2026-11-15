/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontier.Computability.Probabilistic.CoinTape
import CslibFrontier.Computability.Complexity.Classes.QMA.MA
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Probability.PMF.Bool
public import CslibFrontier.Probability.PMF.Coin

/-!
# Native zero-query circuits for classical probabilistic programs

A strict probabilistic polynomial-time program on bit words has an exact native quantum
realization. The construction first replaces the program by a deterministic polynomial-time
evaluator with a fixed polynomial number of fair seed bits. A Boolean circuit family computes
that evaluator, `UniformVerifierFamily.ofMA` prepares only the fresh seed suffix with Hadamard
gates, and an oracle-family wrapper supplies the unchanged encoded `(security parameter,
challenge)` word as the classical prefix.

The resulting family has no quantum input and makes no oracle query. Its terminal decision law is
exactly the original probabilistic program law, rather than an approximation. Circuit resources
and offline generator resources remain separate: `resourcesOfCircuitFamily` gives the exact four
online/artifact coordinates, while the returned `GeneratorCertificate` exposes generator code,
time, workspace and the same description word as its output coordinate.

The construction and results are original formalization infrastructure.

## Main definitions

* `Cslib.Quantum.UniformOracleCircuitFamily.ofCircuitFamily`: view a uniform circuit family as a
  zero-query oracle family on the complete encoded classical input.
* `Cslib.Quantum.UniformOracleCircuitFamily.resourcesOfCircuitFamily`: its exact circuit-resource
  coordinates.

## Main results

* `Cslib.Quantum.UniformOracleCircuitFamily.decisionLaw_ofCircuitFamily`: the wrapper's exact
  Boolean decision law.
* `Cslib.Probability.IsPPTOn.exists_uniformOracleCircuitFamily`: a strict PPT Boolean word program
  has a zero-query native realization with exactly the same decision law and an offline generator
  certificate.
-/

@[expose] public section

namespace Cslib.Quantum.UniformOracleCircuitFamily

open Turing.MultiTapeTM

/-- A uniform circuit family viewed as a zero-query oracle family. At parameter `n` and challenge
length `ℓ`, the circuit receives the complete word `encPair encUnary encBits (n, challenge)`.
It has no quantum input, returns its decision qubit, and embeds every ordinary gate as a
non-phase oracle-circuit instruction. -/
def ofCircuitFamily (F : UniformCircuitFamily) : UniformOracleCircuitFamily where
  description n ℓ :=
    { width := F.width (2 * n + 1 + ℓ)
      queryWidth := 0
      responseWidth := 0
      quantumInputWidth := 0
      outputWidth := 1
      instructions := (F.gates (2 * n + 1 + ℓ)).map fun g => .gate (false, g) }
  computableInPolyTime_description := by
    have hsecurity : ComputableInPolyTime OracleInputSize.securityParameter
        encOracleInputSize encUnary :=
      encOracleInputSize_securityParameter_polyTime ComputableInPolyTime.id'
    have hclassical : ComputableInPolyTime OracleInputSize.classicalInputLength
        encOracleInputSize encUnary :=
      encOracleInputSize_classicalInputLength_polyTime ComputableInPolyTime.id'
    have hinputLength : ComputableInPolyTime
        (fun s : OracleInputSize => 2 * s.securityParameter + 1 + s.classicalInputLength)
        encOracleInputSize encUnary :=
      ComputableInPolyTime.unary_add'
        (ComputableInPolyTime.unary_add'
          (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const 2) hsecurity)
          (ComputableInPolyTime.const 1)) hclassical
    have hwidth : ComputableInPolyTime
        (fun s : OracleInputSize => F.width (2 * s.securityParameter + 1 + s.classicalInputLength))
        encOracleInputSize encUnary := F.computableInPolyTime_width.comp hinputLength
    have hphase : ComputableInPolyTime (fun g : GateCode => (false, g))
        encGateCode encPhaseGateCode := (ComputableInPolyTime.const false).prod
          ComputableInPolyTime.id'
    have horacle : ComputableInPolyTime
        (fun g : GateCode => OracleGateCode.gate (false, g)) encGateCode encOracleGateCode :=
      OracleGateCode.computableInPolyTime_gate hphase
    have hmap : ComputableInPolyTime
        (List.map fun g : GateCode => OracleGateCode.gate (false, g))
        (encList encGateCode) (encList encOracleGateCode) :=
      (ComputableTidilyInPolyTime.map horacle.tidy).computableInPolyTime
    have hgates : ComputableInPolyTime
        (fun s : OracleInputSize =>
          (F.gates (2 * s.securityParameter + 1 + s.classicalInputLength)).map
            fun g => OracleGateCode.gate (false, g))
        encOracleInputSize (encList encOracleGateCode) :=
      hmap.comp (F.computableInPolyTime_gates.comp hinputLength)
    exact encOracleCircuitDescription_mk_polyTime hwidth (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.const 0) (ComputableInPolyTime.const 0)
      (ComputableInPolyTime.const 1) hgates
  wellFormed n ℓ := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · change 2 * n + 1 + ℓ ≤ F.width (2 * n + 1 + ℓ)
      exact F.le_width _
    · change 0 + 0 ≤ F.width (2 * n + 1 + ℓ)
      omega
    · change 1 ≤ F.width (2 * n + 1 + ℓ)
      exact F.width_pos _
    intro instruction hinstruction
    change instruction ∈ (F.gates (2 * n + 1 + ℓ)).map
      (fun g => OracleGateCode.gate (false, g)) at hinstruction
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hinstruction
    exact F.wellFormed _ g hg

/-- The exact online/artifact coordinates of `ofCircuitFamily`: active qubits, elementary gates,
zero queries and the complete encoded description length. -/
def resourcesOfCircuitFamily (F : UniformCircuitFamily) (n ℓ : ℕ) :
    OracleCircuit.Resources :=
  ⟨F.width (2 * n + 1 + ℓ), (F.gates (2 * n + 1 + ℓ)).length, 0,
    (encOracleCircuitDescription ((ofCircuitFamily F).description n ℓ)).length⟩

/-- The ordinary circuit wrapper meets its qubit, gate, zero-query and full-description budgets
componentwise. -/
theorem within_resources_ofCircuitFamily (F : UniformCircuitFamily) (n ℓ : ℕ) :
    OracleCircuit.Within ((ofCircuitFamily F).description n ℓ).instructions
      ((ofCircuitFamily F).description n ℓ).width
      (encOracleCircuitDescription ((ofCircuitFamily F).description n ℓ)).length
      (resourcesOfCircuitFamily F n ℓ) := by
  have hcounts :
      OracleCircuit.gateCount ((ofCircuitFamily F).description n ℓ).instructions =
          (F.gates (2 * n + 1 + ℓ)).length ∧
        OracleCircuit.queryCount ((ofCircuitFamily F).description n ℓ).instructions = 0 := by
    change OracleCircuit.gateCount
        ((F.gates (2 * n + 1 + ℓ)).map fun g => OracleGateCode.gate (false, g)) = _ ∧
      OracleCircuit.queryCount
        ((F.gates (2 * n + 1 + ℓ)).map fun g => OracleGateCode.gate (false, g)) = _
    simp [OracleCircuit.gateCount, OracleCircuit.queryCount,
      OracleGateCode.isQuery, List.countP_map, Function.comp_def]
  rw [OracleCircuit.Within, hcounts.1, hcounts.2]
  exact ⟨le_rfl, le_rfl, le_rfl, le_rfl⟩

private theorem decisionLaw_ofCircuitFamily_apply_true (F : UniformCircuitFamily) (n : ℕ)
    (x : List Bool)
    (H : (Fin ((ofCircuitFamily F).description n x.length).queryWidth → Bool) →
      Fin ((ofCircuitFamily F).description n x.length).responseWidth → Bool) :
    (((ofCircuitFamily F).output n x H (ket fun _ => false) (norm_ket _)).map
      fun output => output.headD false) true =
        ENNReal.ofReal (F.acceptProb (encPair encUnary encBits (n, x))) := by
  let word := encPair encUnary encBits (n, x)
  have hword : word.length = 2 * n + 1 + x.length := by
    simp [word, encUnary_apply]
  have hrun :
      (ofCircuitFamily F).run n x H (ket fun _ => false) =
        Circuit.run
          (Circuit.ofCodes (F.width (2 * n + 1 + x.length))
            (F.gates (2 * n + 1 + x.length)))
          (inputState (F.width (2 * n + 1 + x.length)) word) := by
    rw [UniformOracleCircuitFamily.run_apply, UniformOracleCircuitFamily.initialState_ket]
    change Circuit.eval
      (OracleCircuit.toCircuit (F.width (2 * n + 1 + x.length)) H
        ((F.gates (2 * n + 1 + x.length)).map
          fun g => OracleGateCode.gate (false, g)))
      (ket (inputState (F.width (2 * n + 1 + x.length))
        (word ++ List.ofFn fun _ : Fin 0 => false))) = _
    have hz : List.ofFn (fun _ : Fin 0 => false) = [] :=
      List.eq_nil_of_length_eq_zero (by simp)
    rw [hz, List.append_nil]
    rw [show ((F.gates (2 * n + 1 + x.length)).map
          fun g => OracleGateCode.gate (false, g)) =
        ((F.gates (2 * n + 1 + x.length)).map fun g => (false, g)).map
          OracleGateCode.gate by simp only [List.map_map]; rfl,
      OracleCircuit.toCircuit_map_gate, Circuit.ofPhaseCodes_map]
    rfl
  have hwidth : 0 < ((ofCircuitFamily F).description n x.length).width := by
    change 0 < F.width (2 * n + 1 + x.length)
    exact F.width_pos _
  have hfiber :
      (Finset.univ.filter fun y :
          Fin ((ofCircuitFamily F).description n x.length).width → Bool =>
        (List.ofFn fun i : Fin 1 =>
          y (Fin.castLEEmb ((ofCircuitFamily F).wellFormed n x.length).output_le i)).headD
            false = true) =
        accepting ((ofCircuitFamily F).description n x.length).width := by
    apply Finset.ext
    intro y
    rw [Finset.mem_filter, mem_accepting hwidth]
    simp only [Finset.mem_univ, true_and, List.ofFn_succ,
      List.ofFn_zero, List.headD_cons]
    have hi : Fin.castLEEmb ((ofCircuitFamily F).wellFormed n x.length).output_le (0 : Fin 1) =
        ⟨0, hwidth⟩ := Fin.ext rfl
    rw [hi]
  rw [UniformOracleCircuitFamily.output_eq, measureOut, PMF.map_comp]
  change measureOut ((ofCircuitFamily F).run n x H (ket fun _ => false)) _
      (fun y => (List.ofFn fun i : Fin 1 =>
        y (Fin.castLEEmb ((ofCircuitFamily F).wellFormed n x.length).output_le i)).headD false)
      true = _
  rw [measureOut_eq_ofReal_measureProb, hfiber, hrun]
  change ENNReal.ofReal (measureProb
      (Circuit.run (Circuit.ofCodes (F.width (2 * n + 1 + x.length))
        (F.gates (2 * n + 1 + x.length)))
        (inputState (F.width (2 * n + 1 + x.length)) word))
      (accepting (F.width (2 * n + 1 + x.length)))) = _
  rw [UniformCircuitFamily.acceptProb, Quantum.acceptProb, hword]

/-- The exact Boolean output law of the zero-query wrapper is the biased coin whose `true`
probability is the ordinary circuit family's acceptance probability on the complete encoded
`(security parameter, challenge)` word. The supplied oracle is irrelevant because the description
contains no query. -/
theorem decisionLaw_ofCircuitFamily (F : UniformCircuitFamily) (n : ℕ) (x : List Bool)
    (H : (Fin ((ofCircuitFamily F).description n x.length).queryWidth → Bool) →
      Fin ((ofCircuitFamily F).description n x.length).responseWidth → Bool) :
    ((ofCircuitFamily F).output n x H (ket fun _ => false) (norm_ket _)).map
        (fun output => output.headD false) =
      Cslib.Probability.PMF.coin
        ⟨F.acceptProb (encPair encUnary encBits (n, x)),
          F.acceptProb_nonneg _, F.acceptProb_le_one _⟩ := by
  apply Cslib.Probability.PMF.ext_bool
  rw [decisionLaw_ofCircuitFamily_apply_true, Cslib.Probability.PMF.coin_apply]
  rfl

end Cslib.Quantum.UniformOracleCircuitFamily

namespace Cslib.Probability

open Cslib.Quantum Finset Turing.MultiTapeTM

/-- A strict probabilistic polynomial-time Boolean program on raw words has one uniform native
zero-query family with exactly the same law on the complete encoded `(security parameter,
challenge)` input. The returned generator certificate keeps its static code, time, workspace and
generated description length as four separate offline coordinates. -/
theorem IsPPTOn.exists_uniformOracleCircuitFamily {program : List Bool → ProbComp Bool}
    (h : IsPPTOn encBits encBool program) :
    ∃ (family : UniformOracleCircuitFamily) (_certificate : family.GeneratorCertificate),
      (∀ n x,
        (family.output n x (fun _ _ => false) (ket fun _ => false) (norm_ket _)).map
            (fun output => output.headD false) =
          ProbComp.eval (program (encPair encUnary encBits (n, x)))) ∧
      (∀ n ℓ,
        OracleCircuit.Within (family.description n ℓ).instructions
          (family.description n ℓ).width
          (encOracleCircuitDescription (family.description n ℓ)).length
          ⟨family.description n ℓ |>.width,
            (family.description n ℓ).instructions.gateCount, 0,
            (encOracleCircuitDescription (family.description n ℓ)).length⟩) := by
  classical
  obtain ⟨c, d, evaluate, hevaluate, hlaw⟩ := h.exists_seeded_evaluator
  obtain ⟨F, hF⟩ := Cslib.Complexity.exists_uniformCircuitFamily hevaluate
  let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ d
  let verifier := UniformVerifierFamily.ofMA F 0 p
  let ordinary := verifier.toUniformCircuitFamily
  let family := UniformOracleCircuitFamily.ofCircuitFamily ordinary
  obtain ⟨certificate⟩ := UniformOracleCircuitFamily.exists_generatorCertificate family
  have hp_eval (m : ℕ) : p.eval m = c * (m + 1) ^ d := by
    simp [p]
  have haccept (word : List Bool) : ordinary.acceptProb word =
      (univ.filter fun r : Fin (p.eval word.length) → Bool =>
        evaluate word (List.ofFn r)).card / 2 ^ p.eval word.length := by
    exact UniformVerifierFamily.acceptProb_ofMA_zeroWitness F p word (evaluate word)
      fun w _ => by simpa only [encPair_apply, encBits_apply] using hF (word, w)
  refine ⟨family, certificate, ?_, ?_⟩
  · intro n x
    rw [UniformOracleCircuitFamily.decisionLaw_ofCircuitFamily]
    apply Cslib.Probability.PMF.ext_bool
    rw [Cslib.Probability.PMF.coin_apply]
    simp only [ite_true]
    rw [hlaw, BitString.uniformList_map_apply, haccept, hp_eval]
    simp only [encBits_apply]
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_ofNat]
    rfl
  · intro n ℓ
    have hresources :=
      UniformOracleCircuitFamily.within_resources_ofCircuitFamily ordinary n ℓ
    rw [OracleCircuit.Within] at hresources ⊢
    exact ⟨le_rfl, le_rfl, hresources.2.2.1, le_rfl⟩

end Cslib.Probability
