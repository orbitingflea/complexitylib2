/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Generator
public import CslibFrontier.Computability.Circuit.Quantum.Output
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Prefix
public import CslibFrontier.Crypto.Game.AttackResources
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.List.UnaryCode

/-!
# Uniform families for finite-width HQC support sampling

`SupportSamplerSchedule` supplies arbitrary unary-computable word-width, value-bit, universe, and
support-weight schedules. The resulting oracle-free circuit family has exactly the finite
`sampleSupport2` law at every security parameter; it does not replace that non-dyadic law by the
ideal fixed-weight distribution. `SupportSamplerSchedule.HasNegligibleError` records the separate
growing-width condition under which the finite discrepancy bound is negligible.

The schedule carries two layout facts needed by the existing unshifted reversible realization:
the framed unary family input fits its active register, and the copied output block is disjoint
from the measured prefix. They are properties of the generated layout, not sampling or security
assumptions.

The circuit-generation and family-composition results are original infrastructure. The exact
finite law and density bound are reused from `SupportCircuit.Sampler` and `SupportProbability`.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean BitString Probability
open Quantum Quantum.GateCode Quantum.Reversible
open Turing.MultiTapeTM ComputableInPolyTime

/-- Polynomial-time parameter schedules and layout facts for one finite HQC support sampler. -/
structure SupportSamplerSchedule where
  /-- Number of fair bits used for each source word. -/
  wordWidth : ℕ → ℕ
  /-- Number of bits used to represent each candidate value. -/
  valueBits : ℕ → ℕ
  /-- Size of the sampled support universe. -/
  universeSize : ℕ → ℕ
  /-- Requested fixed support weight. -/
  supportWeight : ℕ → ℕ
  /-- The word-width schedule is polynomial-time computable in unary. -/
  computableInPolyTime_wordWidth : ComputableInPolyTime wordWidth encUnary encUnary
  /-- The value-bit schedule is polynomial-time computable in unary. -/
  computableInPolyTime_valueBits : ComputableInPolyTime valueBits encUnary encUnary
  /-- The universe schedule is polynomial-time computable in unary. -/
  computableInPolyTime_universeSize : ComputableInPolyTime universeSize encUnary encUnary
  /-- The support-weight schedule is polynomial-time computable in unary. -/
  computableInPolyTime_supportWeight : ComputableInPolyTime supportWeight encUnary encUnary
  /-- Every requested support fits in its universe. -/
  supportWeight_le_universeSize : ∀ s, supportWeight s ≤ universeSize s
  /-- Every universe value fits in the declared binary representation. -/
  universeSize_lt_two_pow_valueBits : ∀ s, universeSize s < 2 ^ valueBits s
  /-- The framed unary security parameter fits the active sampler register. -/
  framedInput_le_activeWidth : ∀ s,
    2 * s + 1 ≤ samplerWidth (supportWeight s * wordWidth s)
      (supportSamplerCircuit (wordWidth s) (valueBits s) (universeSize s)
        (supportWeight s)).code
  /-- The copied output block begins after the measured prefix. -/
  outputPrefix_disjoint : ∀ s,
    universeSize s ≤ samplerOutputStart (supportWeight s * wordWidth s)
      (supportSamplerCircuit (wordWidth s) (valueBits s) (universeSize s)
        (supportWeight s)).code

namespace SupportSamplerSchedule

variable (S : SupportSamplerSchedule)

/-- Boolean support sampler selected by a parameter schedule. -/
@[expose] def circuit (s : ℕ) : Circuit signature
    (S.supportWeight s * S.wordWidth s) (S.universeSize s) :=
  supportSamplerCircuit (S.wordWidth s) (S.valueBits s) (S.universeSize s)
    (S.supportWeight s)

/-- Number of independent fair seed bits at a security parameter. -/
@[expose] def seedBits (s : ℕ) : ℕ := S.supportWeight s * S.wordWidth s

/-- Active register width of the reversible sampler, before auxiliary-input allowance. -/
@[expose] def activeWidth (s : ℕ) : ℕ := samplerWidth (S.seedBits s) (S.circuit s).code

/-- The finite discrepancy bound inherited from the multiply-high support sampler. -/
@[expose] noncomputable def finiteError (s : ℕ) : NNReal := Real.toNNReal
  (1 - (supportLowerDensity (S.wordWidth s) (S.universeSize s) 0
    (S.supportWeight s)).toReal)

/-- The schedule grows sufficiently when its density-derived discrepancy bound is negligible. -/
@[expose] def HasNegligibleError : Prop := Negligible S.finiteError

/-- The scheduled Boolean circuit retains the exact finite `sampleSupport2` law. -/
theorem samplerDist_circuit (s : ℕ) :
    samplerDist (S.circuit s) =
      (ProbComp.eval (sampleSupport2 (S.wordWidth s) (S.universeSize s)
        (S.supportWeight s))).map (indicatorVector (S.universeSize s)) :=
  samplerDist_supportSamplerCircuit (S.supportWeight_le_universeSize s)
    (S.universeSize_lt_two_pow_valueBits s)

/-- The scheduled finite law is close to the ideal fixed-weight law by the density-derived error
bound. -/
theorem samplerDist_closeTo_ideal (s : ℕ) :
    CloseTo (samplerDist (S.circuit s))
      ((PMF.uniformOfFinset ((Finset.range (S.universeSize s)).powersetCard
        (S.supportWeight s)) (Finset.powersetCard_nonempty.mpr
          (by simpa only [Finset.card_range] using S.supportWeight_le_universeSize s))).map
            (indicatorVector (S.universeSize s)))
      (S.finiteError s : ENNReal) :=
  supportSamplerDist_closeTo_ideal (S.supportWeight_le_universeSize s)
    (S.universeSize_lt_two_pow_valueBits s)

private theorem computableInPolyTime_circuitCode :
    ComputableInPolyTime (fun s => (S.circuit s).code) encUnary encCode :=
  computableInPolyTime_supportSamplerCircuit S.computableInPolyTime_wordWidth
    S.computableInPolyTime_valueBits S.computableInPolyTime_universeSize
    S.computableInPolyTime_supportWeight

private theorem computableInPolyTime_seedBits :
    ComputableInPolyTime S.seedBits encUnary encUnary := by
  unfold seedBits
  exact unary_mul' S.computableInPolyTime_supportWeight
    S.computableInPolyTime_wordWidth

/-- Clear the framed unary family input, prepare the fair seeds, run the reversible sampler, and
move its output block to the measured prefix. -/
@[expose] def gateCodes (s : ℕ) : List GateCode :=
  flipCodes (List.range (2 * s)) ++
    samplerCodes (S.seedBits s) (S.circuit s).code ++
    prefixSwapCodes (samplerOutputStart (S.seedBits s) (S.circuit s).code)
      (S.universeSize s)

/-- The complete scheduled gate list is generated in polynomial time from unary `s`. -/
@[fun_prop] theorem computableInPolyTime_gateCodes :
    ComputableInPolyTime S.gateCodes encUnary (encList encGateCode) := by
  have hseed := S.computableInPolyTime_seedBits
  have hcode := S.computableInPolyTime_circuitCode
  have hsampler := computableInPolyTime_samplerCodes hseed hcode
  have hsource : ComputableInPolyTime
      (fun s => samplerOutputStart (S.seedBits s) (S.circuit s).code)
      encUnary encUnary := computableInPolyTime_samplerOutputStart hseed hcode
  have hprefix := computableInPolyTime_prefixSwapCodes hsource
    S.computableInPolyTime_universeSize
  unfold gateCodes flipCodes
  fun_prop

/-- Flipping the framed unary security parameter clears the initialized basis word for empty
auxiliary input. No deterministic input bit is used as a fair sampler seed. -/
private theorem classicalRun_clearInput {s width : ℕ} (hwidth : 2 * s + 1 ≤ width) :
    classicalRun (flipCodes (List.range (2 * s)))
      (inputState width (encPair encUnary encBits (s, []))) = inputState width [] := by
  apply funext_readBit
  intro c
  rw [readBit_classicalRun_flipCodes List.nodup_range
    (by intro j hj; have := List.mem_range.mp hj; omega)]
  rw [readBit_inputState (by simp [encUnary_apply]; omega),
    readBit_inputState (by simp)]
  simp only [encPair_apply, encUnary_apply, encBits_apply, List.append_nil,
    frame_replicate_true]
  by_cases hc : c ≤ 2 * s
  · rw [List.getD_replicate_true_append_false_of_le [] hc]
    simp only [List.mem_range, List.getD_nil]
    by_cases hlt : c < 2 * s <;> simp [hlt]
  · have hc' : 2 * s + 1 ≤ c := by omega
    have hlen : (List.replicate (2 * s) true ++ [false]).length ≤ c := by
      simp only [List.length_append, List.length_replicate, List.length_singleton]
      omega
    rw [List.getD_eq_default _ _ hlen]
    have hnot : ¬c < 2 * s := by omega
    simp [List.mem_range, hnot]

private theorem run_gateCodes (s : ℕ) :
    Circuit.run (Circuit.ofCodes (S.activeWidth s) (S.gateCodes s))
        (inputState (S.activeWidth s) (encPair encUnary encBits (s, []))) =
      Circuit.eval (Circuit.ofCodes (S.activeWidth s)
          (prefixSwapCodes
            (samplerOutputStart (S.seedBits s) (S.circuit s).code)
            (S.universeSize s)))
        (Circuit.run (Circuit.ofCodes (S.activeWidth s)
            (samplerCodes (S.seedBits s) (S.circuit s).code))
          (inputState (S.activeWidth s) [])) := by
  have hwidth : 2 * s + 1 ≤ S.activeWidth s := by
    change 2 * s + 1 ≤ samplerWidth (S.supportWeight s * S.wordWidth s)
      (supportSamplerCircuit (S.wordWidth s) (S.valueBits s) (S.universeSize s)
        (S.supportWeight s)).code
    exact S.framedInput_le_activeWidth s
  have hclear : IsClassical (S.activeWidth s) (flipCodes (List.range (2 * s))) :=
    isClassical_flipCodes (by
      intro j hj
      have hj' := List.mem_range.mp hj
      omega)
  rw [Circuit.run, gateCodes, Circuit.ofCodes_append, Circuit.ofCodes_append,
    Quantum.Circuit.eval_append, Quantum.Circuit.eval_append,
    Circuit.eval_ofCodes_ket hclear,
    classicalRun_clearInput hwidth]
  rw [Quantum.Circuit.run]

/-- Starting from the framed empty input, the complete gate list realizes exactly the scheduled
Boolean sampler law. Input clearing and output-prefix movement add no approximation. -/
theorem measureOut_gateCodes (s : ℕ) :
    measureOut
        (Circuit.run (Circuit.ofCodes (S.activeWidth s) (S.gateCodes s))
          (inputState (S.activeWidth s) (encPair encUnary encBits (s, []))))
        (Circuit.norm_run _ _) (blockReadout 0 (S.universeSize s)) =
      samplerDist (S.circuit s) := by
  let source := samplerOutputStart (S.seedBits s) (S.circuit s).code
  let ψ : Qubits (S.activeWidth s) := Circuit.run
    (Circuit.ofCodes (S.activeWidth s) (samplerCodes (S.seedBits s) (S.circuit s).code))
    (inputState (S.activeWidth s) [])
  have hψ : ‖ψ‖ = 1 := by
    dsimp only [ψ]
    exact Circuit.norm_run _ _
  have hrun :
      Circuit.run (Circuit.ofCodes (S.activeWidth s) (S.gateCodes s))
          (inputState (S.activeWidth s) (encPair encUnary encBits (s, []))) =
        Circuit.eval
          (Circuit.ofCodes (S.activeWidth s) (prefixSwapCodes source (S.universeSize s))) ψ := by
    simpa only [source, ψ] using S.run_gateCodes s
  have hdisjoint : S.universeSize s ≤ source := by
    change S.universeSize s ≤ samplerOutputStart
      (S.supportWeight s * S.wordWidth s)
      (supportSamplerCircuit (S.wordWidth s) (S.valueBits s) (S.universeSize s)
        (S.supportWeight s)).code
    exact S.outputPrefix_disjoint s
  have hfit : source + S.universeSize s ≤ S.activeWidth s := by
    unfold source activeWidth seedBits circuit samplerWidth
    simp only [Circuit.code, List.length_ofFn]
    omega
  calc
    measureOut
        (Circuit.run (Circuit.ofCodes (S.activeWidth s) (S.gateCodes s))
          (inputState (S.activeWidth s) (encPair encUnary encBits (s, []))))
        (Circuit.norm_run _ _) (blockReadout 0 (S.universeSize s)) =
      measureOut
        (Circuit.eval
          (Circuit.ofCodes (S.activeWidth s) (prefixSwapCodes source (S.universeSize s))) ψ)
        (by rw [Circuit.norm_eval, hψ]) (blockReadout 0 (S.universeSize s)) := by
          congr 1
    _ = measureOut ψ hψ (blockReadout source (S.universeSize s)) :=
      measureOut_eval_prefixSwapCodes hdisjoint hfit ψ hψ
    _ = samplerDist (S.circuit s) := by
      change measureOut ψ hψ (samplerReadout (S.circuit s)) = samplerDist (S.circuit s)
      simp only [ψ, activeWidth, seedBits, samplerDist]
      congr 1

/-- Exact finite oracle-free description at a security parameter and auxiliary-input length. -/
@[expose] def description (s ℓ : ℕ) : OracleCircuitDescription where
  width := S.activeWidth s + ℓ
  queryWidth := 0
  responseWidth := 0
  quantumInputWidth := 0
  outputWidth := S.universeSize s
  instructions := (S.gateCodes s).map fun g => OracleGateCode.gate (false, g)

private theorem computableInPolyTime_activeWidth :
    ComputableInPolyTime S.activeWidth encUnary encUnary :=
  computableInPolyTime_samplerWidth S.computableInPolyTime_seedBits
    S.computableInPolyTime_circuitCode

private theorem computableInPolyTime_description :
    ComputableInPolyTime
      (fun input : OracleInputSize => S.description input.securityParameter
        input.classicalInputLength)
      encOracleInputSize encOracleCircuitDescription := by
  have hs : ComputableInPolyTime
      (fun input : OracleInputSize => input.securityParameter) encOracleInputSize encUnary := by
    fun_prop
  have hℓ : ComputableInPolyTime
      (fun input : OracleInputSize => input.classicalInputLength) encOracleInputSize encUnary := by
    fun_prop
  have hwidth := S.computableInPolyTime_activeWidth
  have huniverse := S.computableInPolyTime_universeSize
  have hphase : ComputableInPolyTime (fun g : GateCode => (false, g))
      encGateCode encPhaseGateCode := (const false).prod id'
  have horacle := OracleGateCode.computableInPolyTime_gate hphase
  have hinstructions := horacle.map.comp (S.computableInPolyTime_gateCodes.comp hs)
  unfold description
  fun_prop

private theorem wellFormed_description (s ℓ : ℕ) :
    (S.description s ℓ).WellFormed ⟨s, ℓ⟩ := by
  let code := (S.circuit s).code
  let seed := S.seedBits s
  let source := samplerOutputStart seed code
  let width := S.activeWidth s
  have hinput : 2 * s + 1 + ℓ ≤ width + ℓ := by
    have h := S.framedInput_le_activeWidth s
    change 2 * s + 1 + ℓ ≤ S.activeWidth s + ℓ
    change 2 * s + 1 + ℓ ≤ width + ℓ
    change 2 * s + 1 ≤ S.activeWidth s at h
    exact Nat.add_le_add_right h ℓ
  have hsource : S.universeSize s ≤ source := by
    change S.universeSize s ≤ samplerOutputStart
      (S.supportWeight s * S.wordWidth s)
      (supportSamplerCircuit (S.wordWidth s) (S.valueBits s) (S.universeSize s)
        (S.supportWeight s)).code
    exact S.outputPrefix_disjoint s
  have hfit : source + S.universeSize s ≤ width := by
    have hlen : code.2.length = S.universeSize s := by
      simp only [code, circuit, Circuit.code, List.length_ofFn]
    change source + S.universeSize s ≤ source + code.2.length
    rw [hlen]
  have hclear : IsClassical width (flipCodes (List.range (2 * s))) :=
    isClassical_flipCodes (by
      intro j hj
      have hj' := List.mem_range.mp hj
      have h := S.framedInput_le_activeWidth s
      change 2 * s + 1 ≤ width at h
      omega)
  have hsampler : ∀ g ∈ samplerCodes seed code, g.WellFormed width := by
    dsimp only [width, seed]
    unfold activeWidth
    simpa only [code] using wellFormed_samplerCodes (S.seedBits s) (S.circuit s).code
  have hprefix : IsClassical width (prefixSwapCodes source (S.universeSize s)) :=
    isClassical_prefixSwapCodes hsource hfit
  refine ⟨hinput, by simp [description], ?_, ?_⟩
  · change S.universeSize s ≤ width + ℓ
    omega
  intro instruction hinstruction
  simp only [description, List.mem_map] at hinstruction
  obtain ⟨g, hg, rfl⟩ := hinstruction
  change OracleGateCode.WellFormed 0 0 (width + ℓ) (.gate (false, g))
  simp only [OracleGateCode.WellFormed, PhaseGateCode.WellFormed]
  have hgwidth : g.WellFormed width := by
    simp only [gateCodes, List.mem_append] at hg
    rcases hg with (hg | hg) | hg
    · exact (hclear g hg).2
    · exact hsampler g hg
    · exact (hprefix g hg).2
  simpa using hgwidth.shift (o := 0) (by omega : 0 + width ≤ width + ℓ)

/-- Native uniform oracle-circuit family realizing one scheduled HQC support draw. The family is
oracle-free; the certified output law below uses empty auxiliary input. -/
def family : UniformOracleCircuitFamily where
  description := S.description
  computableInPolyTime_description := S.computableInPolyTime_description
  wellFormed := S.wellFormed_description

private theorem output_family_eq_measureOut (s : ℕ) :
    S.family.output s [] (fun _ _ => false) (ket (fun _ => false)) (norm_ket _) =
      (measureOut
        (Circuit.run (Circuit.ofCodes (S.activeWidth s) (S.gateCodes s))
          (inputState (S.activeWidth s) (encPair encUnary encBits (s, []))))
        (Circuit.norm_run _ _) (blockReadout 0 (S.universeSize s))).map List.ofFn := by
  let H : (Fin (S.family.description s 0).queryWidth → Bool) →
      Fin (S.family.description s 0).responseWidth → Bool := fun _ _ => false
  let z : Fin (S.family.description s 0).quantumInputWidth → Bool := fun _ => false
  let ψ : Qubits (S.family.description s 0).width :=
    Circuit.eval
      (OracleCircuit.toCircuit (S.family.description s 0).width H
        (S.family.description s 0).instructions)
      (ket (inputState (S.family.description s 0).width
        (encPair encUnary encBits (s, ([] : List Bool)) ++ List.ofFn z)))
  have hψ : ‖ψ‖ = 1 := by
    dsimp only [ψ]
    rw [Circuit.norm_eval, norm_ket]
  calc
    S.family.output s [] (fun _ _ => false) (ket (fun _ => false)) (norm_ket _) =
      measureOut ψ hψ (fun y => List.ofFn fun i =>
        y (Fin.castLEEmb (S.family.wellFormed s 0).output_le i)) := by
      convert (UniformOracleCircuitFamily.output_ket S.family s ([] : List Bool) H z) using 1
    _ = measureOut ψ hψ (fun y => List.ofFn
          (blockReadout 0 (S.family.description s 0).outputWidth y)) := by
      congr 1
      exact listOfFn_castLEEmb_eq_blockReadout (S.family.wellFormed s 0).output_le
    _ = (measureOut ψ hψ
        (blockReadout 0 (S.family.description s 0).outputWidth)).map List.ofFn :=
      (measureOut_map ψ hψ _ List.ofFn).symm
    _ = _ := by
      simp only [H, z, ψ, family, description, List.ofFn_zero, List.append_nil, Nat.add_zero]
      simp only [OracleCircuit.toCircuit_map_gateCode, Quantum.Circuit.run]
      congr 1

/-- On empty auxiliary input, the uniform family returns exactly the scheduled finite
`sampleSupport2` indicator law. -/
theorem output_family (s : ℕ) :
    S.family.output s [] (fun _ _ => false) (ket (fun _ => false)) (norm_ket _) =
      ((ProbComp.eval (sampleSupport2 (S.wordWidth s) (S.universeSize s)
        (S.supportWeight s))).map (indicatorVector (S.universeSize s))).map List.ofFn := by
  rw [S.output_family_eq_measureOut, S.measureOut_gateCodes, S.samplerDist_circuit]

/-- The uniform-family output is close to the ideal fixed-weight indicator law by the scheduled
finite-width error. -/
theorem output_family_closeTo_ideal (s : ℕ) :
    CloseTo
      (S.family.output s [] (fun _ _ => false) (ket (fun _ => false)) (norm_ket _))
      (((PMF.uniformOfFinset ((Finset.range (S.universeSize s)).powersetCard
        (S.supportWeight s)) (Finset.powersetCard_nonempty.mpr
          (by simpa only [Finset.card_range] using S.supportWeight_le_universeSize s))).map
            (indicatorVector (S.universeSize s))).map List.ofFn)
      (S.finiteError s : ENNReal) := by
  rw [S.output_family_eq_measureOut, S.measureOut_gateCodes]
  exact (S.samplerDist_closeTo_ideal s).map List.ofFn

/-- Exact online-circuit and finite-description resources of the generated artifact. These
coordinates exclude generator time, workspace, and static generator code. -/
@[expose] def circuitResources (s ℓ : ℕ) : OracleCircuit.Resources :=
  let D := S.description s ℓ
  ⟨D.width, D.instructions.gateCount, D.instructions.queryCount,
    (encOracleCircuitDescription D).length⟩

/-- The generated finite artifact fits its exact online and description coordinates. -/
theorem within_circuitResources (s ℓ : ℕ) :
    OracleCircuit.Within (S.description s ℓ).instructions (S.description s ℓ).width
      (encOracleCircuitDescription (S.description s ℓ)).length (S.circuitResources s ℓ) := by
  simp [circuitResources, OracleCircuit.Within]

/-- Every generated description is oracle-free. -/
@[simp] theorem queryCount_description (s ℓ : ℕ) :
    (S.description s ℓ).instructions.queryCount = 0 := by
  simp [description, OracleCircuit.queryCount, OracleGateCode.isQuery]

/-- One retained generator occurrence and one retained generated-description occurrence. The
second is the description already charged by `circuitResources.descriptionBits`. -/
@[expose] def installedArtifacts (certificate : S.family.GeneratorCertificate) (s : ℕ) :
    List Crypto.Game.InstalledArtifact :=
  [{ kind := .generator, bits := (certificate.resources ⟨s, 0⟩).codeBits },
    { kind := .generatedProgram, bits := (certificate.resources ⟨s, 0⟩).outputBits }]

/-- The artifact inventory charges the exact static universal-machine description once. -/
theorem installedBits_generator (certificate : S.family.GeneratorCertificate) (s : ℕ) :
    Crypto.Game.InstalledArtifact.installedBits (S.installedArtifacts certificate s) .generator =
      (Turing.MultiTapeTM.Universal.eDesc certificate.code).length := by
  simp [installedArtifacts, Crypto.Game.InstalledArtifact.installedBits,
    UniformOracleCircuitFamily.GeneratorCertificate.resources]

/-- The artifact inventory charges the exact generated description once. -/
theorem installedBits_generatedProgram (certificate : S.family.GeneratorCertificate) (s : ℕ) :
    Crypto.Game.InstalledArtifact.installedBits (S.installedArtifacts certificate s)
        .generatedProgram =
      (encOracleCircuitDescription (S.description s 0)).length := by
  simp [installedArtifacts, Crypto.Game.InstalledArtifact.installedBits,
    UniformOracleCircuitFamily.GeneratorCertificate.resources, family]

/-- The uniform family has a deterministic generator certificate whose static code, offline
time, workspace, and exact output size are polynomial on the schedule. -/
theorem exists_generator :
    ∃ certificate : S.family.GeneratorCertificate,
      UniformOracleCircuitFamily.GeneratorResources.IsPolynomial
        (fun s => certificate.resources ⟨s, 0⟩) := by
  obtain ⟨certificate⟩ := S.family.exists_generatorCertificate
  refine ⟨certificate, certificate.resources_isPolynomial ?_⟩
  simpa only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
    encUnary_apply, List.length_replicate, Nat.add_zero] using
      (((PolynomiallyBounded.const 2).mul .id).add (.const 1))

end SupportSamplerSchedule

end Cslib.Crypto.HQC
