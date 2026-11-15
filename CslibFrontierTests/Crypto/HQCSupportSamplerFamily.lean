/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test client)

public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Checked clients for scheduled HQC support-sampler families

These examples instantiate the generic family with growing widths. They check its exact
fixed-weight output law, oracle-free resource record, negligible finite-width error, and separate
offline artifact accounting. They do not state an HQC security claim.
-/

public section

namespace CslibFrontierTests.HQCSupportSamplerFamily

open Cslib Cslib.Crypto.HQC Cslib.Quantum Cslib.Probability Cslib.BitString
open Cslib.Quantum.Reversible
open Turing.MultiTapeTM ComputableInPolyTime

private def secretSchedule : SupportSamplerSchedule where
  wordWidth := fun s => 2 * s + 3
  valueBits := fun _ => 2
  universeSize := fun _ => 3
  supportWeight := fun _ => 2
  computableInPolyTime_wordWidth :=
    unary_add' (unary_mul' (const 2) id') (const 3)
  computableInPolyTime_valueBits := const 2
  computableInPolyTime_universeSize := const 3
  computableInPolyTime_supportWeight := const 2
  supportWeight_le_universeSize := by intro; omega
  universeSize_lt_two_pow_valueBits := by intro; norm_num
  framedInput_le_activeWidth := by
    intro s
    unfold samplerWidth samplerOutputStart samplerZero
    omega
  outputPrefix_disjoint := by
    intro s
    unfold samplerOutputStart samplerZero
    omega

theorem output_shape (S : SupportSamplerSchedule) (s : ℕ) {out : List Bool}
    (hout : out ∈ (S.family.output s [] (fun _ _ => false)
      (ket (fun _ => false)) (norm_ket _)).support) :
    out.length = S.universeSize s ∧ out.count true = S.supportWeight s := by
  rw [S.output_family] at hout
  obtain ⟨word, hword, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout
  obtain ⟨A, hA, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hword
  obtain ⟨hsub, hcard⟩ := Finset.mem_powersetCard.mp
    (sampleSupport2_mem_powersetCard (S.supportWeight_le_universeSize s) hA)
  exact ⟨List.length_ofFn, by rw [count_true_ofFn, weight_indicatorVector hsub, hcard]⟩

-- The generic single-draw family has an inhabited exact fixed-weight output law.
example (s : ℕ) :
    ∃ out ∈ (secretSchedule.family.output s [] (fun _ _ => false)
      (ket (fun _ => false)) (norm_ket _)).support,
        out.length = 3 ∧ out.count true = 2 := by
  obtain ⟨out, hout⟩ := (secretSchedule.family.output s [] (fun _ _ => false)
    (ket (fun _ => false)) (norm_ket _)).support_nonempty
  refine ⟨out, hout, ?_⟩
  simpa [secretSchedule] using output_shape secretSchedule s hout

-- Growing word width establishes the explicit asymptotic premise; fixed width 32 would not.
example : secretSchedule.HasNegligibleError := by
  unfold SupportSamplerSchedule.HasNegligibleError SupportSamplerSchedule.finiteError
  apply negligible_one_sub_supportLowerDensity
    (width := fun s => 2 * s + 3) (n := fun _ => 3) (count := fun _ => 2)
  · intro s
    omega
  · exact .const 3
  · exact .const 2
  · intro s
    omega

-- Every generated description is oracle-free and fits its exact online resource record.
example (s ℓ : ℕ) :
    OracleCircuit.Within (secretSchedule.description s ℓ).instructions
        (secretSchedule.description s ℓ).width
        (encOracleCircuitDescription (secretSchedule.description s ℓ)).length
        (secretSchedule.circuitResources s ℓ) ∧
      (secretSchedule.description s ℓ).instructions.queryCount = 0 :=
  ⟨secretSchedule.within_circuitResources s ℓ, secretSchedule.queryCount_description s ℓ⟩

-- Offline generation is polynomial, while the retained generator and generated program are
-- charged as two distinct exact occurrences.
example :
    ∃ certificate : secretSchedule.family.GeneratorCertificate,
      UniformOracleCircuitFamily.GeneratorResources.IsPolynomial
          (fun s => certificate.resources ⟨s, 0⟩) ∧
        ∀ s,
          Crypto.Game.InstalledArtifact.installedBits
              (secretSchedule.installedArtifacts certificate s) .generator =
              (Turing.MultiTapeTM.Universal.eDesc certificate.code).length ∧
            Crypto.Game.InstalledArtifact.installedBits
              (secretSchedule.installedArtifacts certificate s) .generatedProgram =
              (encOracleCircuitDescription (secretSchedule.description s 0)).length := by
  obtain ⟨certificate, hpoly⟩ := secretSchedule.exists_generator
  refine ⟨certificate, hpoly, fun s => ⟨?_, ?_⟩⟩
  · exact secretSchedule.installedBits_generator certificate s
  · exact secretSchedule.installedBits_generatedProgram certificate s

end CslibFrontierTests.HQCSupportSamplerFamily
