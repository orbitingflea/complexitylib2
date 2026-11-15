/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test client)

public import CslibFrontier.Computability.Circuit.Quantum.Oracle.FromPPT
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Classical PPT programs as native zero-query circuits

An ordinary deterministic Boolean program reads the final challenge bit and exercises the exact
decision-law bridge, zero-query resource bound and all four offline generator-resource
coordinates.
-/

public section

namespace CslibFrontierTests.QuantumOracleFromPPT

open Cslib Cslib.Probability Cslib.Quantum Turing.MultiTapeTM
open Cslib.Quantum.UniformOracleCircuitFamily

example :
    ∃ (family : UniformOracleCircuitFamily) (certificate : family.GeneratorCertificate),
      (forall n x,
        (family.output n x (fun _ _ => false) (ket fun _ => false) (norm_ket _)).map
            (fun output => output.headD false) =
          PMF.pure ((encPair encUnary encBits (n, x)).reverse.headD false)) ∧
      (family.output 0 [true] (fun _ _ => false) (ket fun _ => false) (norm_ket _)).map
          (fun output => output.headD false) = PMF.pure true ∧
      (forall n ell,
        OracleCircuit.Within (family.description n ell).instructions
          (family.description n ell).width
          (encOracleCircuitDescription (family.description n ell)).length
          ⟨family.description n ell |>.width,
            (family.description n ell).instructions.gateCount, 0,
            (encOracleCircuitDescription (family.description n ell)).length⟩) ∧
      (forall input,
        Universal.simulate certificate.code
            (List.map Universal.eBit (encOracleInputSize input))
            (certificate.time (encOracleInputSize input).length) =
          (List.map Universal.eBit (encOracleCircuitDescription
            (family.description input.securityParameter input.classicalInputLength)), true)) ∧
      GeneratorResources.IsPolynomial
        (fun n => certificate.resources ⟨n, n + 1⟩) := by
  have hppt : IsPPTOn encBits encBool
      (fun word : List Bool => pure (word.reverse.headD false)) :=
    ((ComputableInPolyTime.headD false).comp ComputableInPolyTime.bitsReverse).isPPTOn
  obtain ⟨family, certificate, hlaw, hresources⟩ := hppt.exists_uniformOracleCircuitFamily
  refine ⟨family, certificate, ?_, ?_, hresources, certificate.computes, ?_⟩
  · intro n x
    simpa using hlaw n x
  · simpa [encPair_apply, frame, encUnary_apply] using hlaw 0 [true]
  · apply certificate.resources_isPolynomial
    simp only [encOracleInputSize_apply, encOracleInputSizeFields, length_encPair,
      encUnary_apply, List.length_replicate]
    fun_prop

end CslibFrontierTests.QuantumOracleFromPPT
