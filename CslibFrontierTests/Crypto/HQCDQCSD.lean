/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.HQC.DQCSD
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.Product
import CslibFrontierTests.Crypto.NativeQuantumIndistinguishability
import Mathlib.Data.Fin.VecNotation

/-! Concrete encodings, source ensembles, and native quantum bridges for HQC DQCSD, and
full-weight families on which both native quantum assumptions fail. -/

public section

namespace CslibFrontierTests.HQCDQCSD

open Cslib Cslib.Crypto Cslib.Crypto.HQC Cslib.Crypto.NativeQuantum Cslib.Quantum
open CslibFrontierTests.NativeQuantumIndistinguishability
open scoped NNReal

/-- A nonvacuous one-bit 2-DQCSD-P family. -/
private def unitParameters : DQCSDParameters where
  blockLength := fun _ => 1
  weight := fun _ => 1
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega

/-- A nonvacuous two-bit family retaining one coordinate in 3-DQCSD-PT. -/
private def truncatedParameters : DQCSDTruncatedParameters where
  blockLength := fun _ => 2
  weight := fun _ => 1
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega
  truncation := fun _ => 1
  truncation_pos := by intro; omega
  truncation_lt := by intro; omega

private def twoSample : SyndromeSample 2 :=
  ⟨![true, false], ![false, true]⟩

private def threeSample : TruncatedSyndromeSample 2 1 :=
  ⟨![true, false], ![false, true], ![true, true], ![false]⟩

-- Both serializers preserve the source tuple order and have no delimiter or variable-width field.
example : twoSample.toWord = [true, false, false, true] := by decide

example : threeSample.toWord = [true, false, false, true, true, true, false] := by decide

example (κ : ℕ) : twoWordLength unitParameters κ = 2 := by rfl

example (κ : ℕ) : threeWordLength truncatedParameters κ = 7 := by rfl

-- The four source ensembles meet the exact fixed-width contracts used by the hardness predicates.
example : SupportsLength (twoRealEnsemble unitParameters (fun _ => true)) (fun _ => 2) := by
  convert supportsLength_twoRealEnsemble unitParameters (fun _ => true) using 1
  funext κ
  rfl

example : SupportsLength (twoUniformEnsemble unitParameters (fun _ => true)) (fun _ => 2) := by
  convert supportsLength_twoUniformEnsemble unitParameters (fun _ => true) using 1
  funext κ
  rfl

example : SupportsLength
    (threeRealEnsemble truncatedParameters (fun _ => true) (fun _ => false)) (fun _ => 7) := by
  convert supportsLength_threeRealEnsemble
    truncatedParameters (fun _ => true) (fun _ => false) using 1
  funext κ
  rfl

example : SupportsLength
    (threeUniformEnsemble truncatedParameters (fun _ => true) (fun _ => false)) (fun _ => 7) := by
  convert supportsLength_threeUniformEnsemble
    truncatedParameters (fun _ => true) (fun _ => false) using 1
  funext κ
  rfl

private theorem test_twoSample_eq_true (κ : ℕ) (sample : SyndromeSample 1)
    (hpublic : parity 1 sample.publicBlock = true) :
    test (bitFamily 0) κ sample.toWord = PMF.pure true := by
  have hbit : sample.publicBlock 0 = true := by
    simpa [parity, parityOn_eq_sum, Fin.sum_univ_succ] using hpublic
  have hword : sample.toWord = true :: [sample.value 0] := by
    rw [SyndromeSample.toWord, List.ofFn_fin_append]
    simp [hbit]
  rw [hword, test_bitFamily]
  rfl

private theorem distinguishingGame_twoReal_unit (κ : ℕ) :
    distinguishingGame (twoRealEnsemble unitParameters (fun _ => true)) (bitFamily 0) κ =
      PMF.pure true := by
  rw [distinguishingGame_eq_bind, twoRealEnsemble, PMF.bind_map]
  apply Probability.PMF.bind_eq_pure_of_forall_mem_support
  intro sample hsample
  apply test_twoSample_eq_true
  exact (parity_of_mem_support_realSyndromeLaw (unitParameters.weight_le κ) true hsample).1

private theorem distinguishingGame_twoUniform_unit (κ : ℕ) :
    distinguishingGame (twoUniformEnsemble unitParameters (fun _ => true)) (bitFamily 0) κ =
      PMF.pure true := by
  rw [distinguishingGame_eq_bind, twoUniformEnsemble, PMF.bind_map]
  apply Probability.PMF.bind_eq_pure_of_forall_mem_support
  intro sample hsample
  apply test_twoSample_eq_true
  simp only [uniformSyndromeLaw, Cslib.Probability.PMF.monad_bind_eq_bind,
    Cslib.Probability.PMF.monad_pure_eq_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsample
  obtain ⟨publicBlock, hpublic, value, _, rfl⟩ := hsample
  exact (BitString.mem_support_uniformParity true publicBlock).mp hpublic

-- The generic native game consumes the exact encoded source words. This deliberately simple
-- first-bit family sees zero gap because both source laws preserve the public parity constraint.
example (κ : ℕ) :
    Game.advantage
      (distinguishingGame (twoRealEnsemble unitParameters (fun _ => true)) (bitFamily 0) κ)
      (distinguishingGame (twoUniformEnsemble unitParameters (fun _ => true)) (bitFamily 0) κ) =
        0 := by
  rw [distinguishingGame_twoReal_unit, distinguishingGame_twoUniform_unit]
  exact Game.advantage_self _

-- Concrete bounds for the instantiated source distributions pass through the source-specific
-- bridge. The assumptions here are intentionally not asserted by the test.
example
    (h : NativeQuantumTwoDQCSDPWithin unitParameters (fun _ => true) (fun _ _ => 0)) :
    NativeQuantumTwoDQCSDP unitParameters (fun _ => true) := by
  apply NativeQuantumTwoDQCSDP.of_within h
  · change PolynomiallyBounded fun _ => 1
    fun_prop
  · fun_prop

example
    (h : NativeQuantumThreeDQCSDPTWithin truncatedParameters
      (fun _ => true) (fun _ => false) (fun _ _ => 0)) :
    NativeQuantumThreeDQCSDPT truncatedParameters (fun _ => true) (fun _ => false) := by
  apply NativeQuantumThreeDQCSDPT.of_within h
  · change PolynomiallyBounded fun _ => 2
    fun_prop
  · fun_prop

/-! ### Full-weight secrets break both assumptions

With block length `2` and weight `2`, every secret block is `11`. A circulant block of even parity
maps `11` to `00`, so with public parity `false` every real syndrome is `11`. The comparison
syndrome is uniform among `00` and `11`. A native circuit reading the first syndrome bit therefore
has advantage `1 / 2`, so neither assumption holds for this family. -/

section FullWeight

open Cslib.BitString

/-- The native distinguishing game of `bitFamily j` reads bit `j` of the sampled word. -/
private theorem distinguishingGame_bitFamily (X : ℕ → PMF (List Bool)) (j n : ℕ) :
    distinguishingGame X (bitFamily j) n = (X n).map fun word => word.getD j false := by
  rw [distinguishingGame_eq_bind, show test (bitFamily j) n = fun x => PMF.pure (x.getD j false)
    from funext (test_bitFamily j n)]
  exact PMF.bind_pure_comp _ _

/-- Bit `0` of a uniform word of either parity is a fair coin. -/
private theorem map_uniformParity_two_apply_zero (b : Bool) :
    (uniformParity 2 b).map (fun word => word 0) = Probability.PMF.uniformOfFintype Bool := by
  rw [uniformParity_eq_map b 1, PMF.map_comp]
  change (Probability.PMF.uniformOfFintype (BitString 1)).map (fun word => word 0) = _
  rw [← Probability.PMF.pi_uniformOfFintype, Probability.PMF.pi_map_eval]

/-- Block length `2` and weight `2`: both secret blocks are `11`. -/
def fullWeightParameters : DQCSDParameters where
  blockLength := fun _ => 2
  weight := fun _ => 2
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega

/-- Full-weight secrets, keeping one of two coordinates of the second syndrome. -/
def fullWeightTruncatedParameters : DQCSDTruncatedParameters where
  blockLength := fun _ => 2
  weight := fun _ => 2
  blockLength_pos := by intro; omega
  weight_pos := by intro; omega
  weight_le := by intro; omega
  truncation := fun _ => 1
  truncation_pos := by intro; omega
  truncation_lt := by intro; omega

/-- With weight-`2` secret blocks and a public block of even parity, the syndrome starts with
`1`. -/
private theorem syndrome_apply_zero_of_weight_two {h x y : BitString 2} (hh : parity 2 h = false)
    (hx : weight x = 2) (hy : weight y = 2) : syndrome h x y 0 = true := by
  revert h x y
  decide

/-- Certain acceptance against a fair coin has advantage `1 / 2`. -/
private theorem advantage_pure_true_uniformOfFintype :
    Game.advantage (PMF.pure true) (Probability.PMF.uniformOfFintype Bool) = 2⁻¹ := by
  rw [Game.advantage_pure_true_left]
  simp [Game.failProbability, Probability.PMF.uniformOfFintype_apply, ENNReal.toNNReal_ofNat]

private theorem distinguishingGame_twoReal_fullWeight (κ : ℕ) :
    distinguishingGame (twoRealEnsemble fullWeightParameters fun _ => false) (bitFamily 2) κ =
      PMF.pure true := by
  rw [distinguishingGame_bitFamily, twoRealEnsemble, PMF.map_comp]
  refine Probability.PMF.map_eq_pure_iff.mpr fun sample hsample => ?_
  simp only [realSyndromeLaw, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff]
    at hsample
  obtain ⟨h, hh, x, hx, y, hy, rfl⟩ := hsample
  exact syndrome_apply_zero_of_weight_two ((mem_support_uniformParity false h).mp hh)
    (mem_weightLayer.mp ((Probability.PMF.mem_support_uniformOfFinset_iff _ x).mp hx))
    (mem_weightLayer.mp ((Probability.PMF.mem_support_uniformOfFinset_iff _ y).mp hy))

private theorem distinguishingGame_twoUniform_fullWeight (κ : ℕ) :
    distinguishingGame (twoUniformEnsemble fullWeightParameters fun _ => false) (bitFamily 2) κ =
      Probability.PMF.uniformOfFintype Bool := by
  rw [distinguishingGame_bitFamily, twoUniformEnsemble, PMF.map_comp]
  change ((uniformSyndromeLaw 2 2 false).map fun sample => sample.value 0) = _
  simp only [uniformSyndromeLaw, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
  rw [show syndromeParity 2 false = false from rfl, PMF.bind_const]
  exact (PMF.bind_pure_comp _ _).trans (map_uniformParity_two_apply_zero false)

/-- **Native quantum 2-DQCSD-P is not vacuous**: it fails for full-weight secrets. -/
theorem not_nativeQuantumTwoDQCSDP_fullWeight :
    ¬ NativeQuantumTwoDQCSDP fullWeightParameters fun _ => false := by
  intro h
  refine not_negligible_const (c := 2⁻¹) (by norm_num)
    ((computationallyIndistinguishable_iff.mp
      ((nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable _ _).mp h)
      (bitFamily 2)).congr fun κ => ?_)
  rw [distinguishingGame_twoReal_fullWeight, distinguishingGame_twoUniform_fullWeight,
    advantage_pure_true_uniformOfFintype]

/-- The concrete form fails too, for every bound that is negligible along polynomial resource
schedules (the bounds `NativeQuantumTwoDQCSDP.of_within` accepts). -/
theorem not_nativeQuantumTwoDQCSDPWithin_fullWeight {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (hε : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun κ => ε κ ⟨qubits κ, gates κ, queries κ⟩)) :
    ¬ NativeQuantumTwoDQCSDPWithin fullWeightParameters (fun _ => false) ε := fun h =>
  not_nativeQuantumTwoDQCSDP_fullWeight <| NativeQuantumTwoDQCSDP.of_within h
    (by change PolynomiallyBounded fun _ => 2; fun_prop) hε

private theorem distinguishingGame_threeReal_fullWeight (κ : ℕ) :
    distinguishingGame
        (threeRealEnsemble fullWeightTruncatedParameters (fun _ => false) fun _ => false)
        (bitFamily 4) κ =
      PMF.pure true := by
  rw [distinguishingGame_bitFamily, threeRealEnsemble, PMF.map_comp]
  refine Probability.PMF.map_eq_pure_iff.mpr fun sample hsample => ?_
  obtain ⟨hh, -, x, -, z, hx, -, hz, hfirst, -⟩ :=
    (mem_support_realTruncatedSyndromeLaw_iff _ _ _ _ sample).mp hsample
  change sample.firstValue 0 = true
  rw [hfirst]
  exact syndrome_apply_zero_of_weight_two hh hx hz

private theorem distinguishingGame_threeUniform_fullWeight (κ : ℕ) :
    distinguishingGame
        (threeUniformEnsemble fullWeightTruncatedParameters (fun _ => false) fun _ => false)
        (bitFamily 4) κ =
      Probability.PMF.uniformOfFintype Bool := by
  rw [distinguishingGame_bitFamily, threeUniformEnsemble, PMF.map_comp]
  change ((uniformTruncatedSyndromeLaw 2 1 2 false false).map fun sample =>
    sample.firstValue 0) = _
  simp only [uniformTruncatedSyndromeLaw, Probability.PMF.monad_bind_eq_bind,
    Probability.PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, PMF.bind_const]
  rw [show syndromeParity 2 false = false from rfl]
  exact (PMF.bind_pure_comp _ _).trans (map_uniformParity_two_apply_zero false)

/-- **Native quantum 3-DQCSD-PT is not vacuous**: it fails for full-weight secrets. -/
theorem not_nativeQuantumThreeDQCSDPT_fullWeight :
    ¬ NativeQuantumThreeDQCSDPT fullWeightTruncatedParameters (fun _ => false) fun _ => false := by
  intro h
  refine not_negligible_const (c := 2⁻¹) (by norm_num)
    ((computationallyIndistinguishable_iff.mp
      ((nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable _ _ _).mp h)
      (bitFamily 4)).congr fun κ => ?_)
  rw [distinguishingGame_threeReal_fullWeight, distinguishingGame_threeUniform_fullWeight,
    advantage_pure_true_uniformOfFintype]

/-- The concrete form fails too, for every bound that is negligible along polynomial resource
schedules (the bounds `NativeQuantumThreeDQCSDPT.of_within` accepts). -/
theorem not_nativeQuantumThreeDQCSDPTWithin_fullWeight
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (hε : ∀ qubits gates queries : ℕ → ℕ,
      PolynomiallyBounded qubits → PolynomiallyBounded gates → PolynomiallyBounded queries →
      Negligible (fun κ => ε κ ⟨qubits κ, gates κ, queries κ⟩)) :
    ¬ NativeQuantumThreeDQCSDPTWithin fullWeightTruncatedParameters (fun _ => false)
      (fun _ => false) ε := fun h =>
  not_nativeQuantumThreeDQCSDPT_fullWeight <| NativeQuantumThreeDQCSDPT.of_within h
    (by change PolynomiallyBounded fun _ => 2; fun_prop) hε

end FullWeight

/-! ### Ordinary-module use through the shared native quantum interfaces -/

theorem twoWithin_sharedInterface (p : DQCSDParameters) (primitive : ℕ → Bool)
    {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumTwoDQCSDPWithin p primitive ε) :
    NativeQuantum.IndistinguishableWithin
      (twoRealEnsemble p primitive)
      (twoUniformEnsemble p primitive)
      (twoWordLength p) ε :=
  (nativeQuantumTwoDQCSDPWithin_iff_indistinguishableWithin p primitive ε).mp h

theorem twoAsymptotic_sharedInterface (p : DQCSDParameters) (primitive : ℕ → Bool)
    (h : NativeQuantumTwoDQCSDP p primitive) :
    NativeQuantum.ComputationallyIndistinguishable
      (twoRealEnsemble p primitive)
      (twoUniformEnsemble p primitive) :=
  (nativeQuantumTwoDQCSDP_iff_computationallyIndistinguishable p primitive).mp h

theorem threeWithin_sharedInterface (p : DQCSDTruncatedParameters)
    (primitive prime : ℕ → Bool) {ε : ℕ → OracleCircuit.Resources → ℝ≥0}
    (h : NativeQuantumThreeDQCSDPTWithin p primitive prime ε) :
    NativeQuantum.IndistinguishableWithin
      (threeRealEnsemble p primitive prime)
      (threeUniformEnsemble p primitive prime)
      (threeWordLength p) ε :=
  (nativeQuantumThreeDQCSDPTWithin_iff_indistinguishableWithin
    p primitive prime ε).mp h

theorem threeAsymptotic_sharedInterface (p : DQCSDTruncatedParameters)
    (primitive prime : ℕ → Bool) (h : NativeQuantumThreeDQCSDPT p primitive prime) :
    NativeQuantum.ComputationallyIndistinguishable
      (threeRealEnsemble p primitive prime)
      (threeUniformEnsemble p primitive prime) :=
  (nativeQuantumThreeDQCSDPT_iff_computationallyIndistinguishable
    p primitive prime).mp h

end CslibFrontierTests.HQCDQCSD
