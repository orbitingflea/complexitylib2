/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Formula
public import CslibFrontier.Computability.Circuit.Pi
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Sampling.Resources
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve
public import CslibFrontier.Crypto.Primitives.HQC.SupportProbability
public import CslibFrontier.Foundations.Data.BitString.Support.Weight
import CslibFrontier.Foundations.Data.BitString.Binary

/-!
# Native circuit sampler for HQC supports

This module composes the existing multiply-high candidate circuit and descending collision circuit,
then turns the corrected word array into the indicator vector used by HQC. Under `count ≤ n` and
`n < 2 ^ bits`, applying the generic reversible sampler gives a native elementary quantum circuit
whose measured output law is exactly `sampleSupport2` mapped through
`BitString.indicatorVector`.

The finite-width law retains the source algorithm's non-dyadic bias. There is no abort branch:
under `count ≤ n` and `n < 2 ^ bits`, every output has weight `count`, while the statistical
discrepancy from the ideal fixed-weight law is bounded by
`1 - (supportLowerDensity width n 0 count).toReal`. The online qubit, gate, query, and full encoded
description coordinates below do not charge the offline generator program or replace the separate
XOF analysis. The instruction-list encoding bound remains a separate construction-derived upper
bound.

## Main definitions

* `Cslib.Crypto.HQC.supportIndicatorCircuit`: membership bits of a corrected word array.
* `Cslib.Crypto.HQC.supportSamplerCircuit`: candidates, collision correction, and indicator output.

## Main results

The semantic and distributional results below assume `count ≤ n` and `n < 2 ^ bits`.

* `Cslib.Crypto.HQC.eval_supportSamplerCircuit`: exact deterministic circuit semantics.
* `Cslib.Crypto.HQC.samplerDist_supportSamplerCircuit`: exact measured `sampleSupport2` law.
* `Cslib.Crypto.HQC.weight_eval_supportSamplerCircuit`: every output has the requested weight.
* `Cslib.Crypto.HQC.supportSamplerDist_closeTo_ideal`: finite-width discrepancy with no abort term.
* `Cslib.Crypto.HQC.supportSamplerWidth`, `Cslib.Crypto.HQC.length_supportSamplerCodes_le`,
  `Cslib.Crypto.HQC.within_supportSamplerCodes`,
  `Cslib.Crypto.HQC.length_encoding_supportSamplerCodes_le`: instantiated online resources.

## References

* [HQC specification, version 5.1][HQC2026], `SampleSupport2`, p. 19, and §6.2.3.
* [J. Watrous, *Quantum computational complexity*][Watrous2008], Section IV.3.
-/

public section

namespace Cslib.Crypto.HQC

open Finset Probability Circuits Circuits.Boolean BitString
open Quantum GateCode Quantum.Reversible Turing.MultiTapeTM

/-- Test whether corrected word `j` is the `bits`-bit representation of `value`. -/
@[expose] def supportWordFormula (bits count value : ℕ) (j : Fin count) :
    Formula signature (count * bits) :=
  Formula.andList (List.ofFn fun k : Fin bits =>
    Formula.literal (fun _ => value.testBit k.val) (finProdFinEquiv (j, k)))

/-- Test whether some corrected word equals `value`. Empty arrays give the constant `false`. -/
@[expose] def supportIndicatorFormula (bits count value : ℕ) :
    Formula signature (count * bits) :=
  Formula.orList (List.ofFn (supportWordFormula bits count value))

/-- Convert the corrected word array into the indicator of its values in `range n`. -/
@[expose] def supportIndicatorCircuit (bits n count : ℕ) :
    Circuit signature (count * bits) n :=
  Circuit.pi fun i => (supportIndicatorFormula bits count i.val).toCircuit

/-- A word-equality formula agrees with `equivFin` when the requested value fits in the word. -/
theorem eval_supportWordFormula {bits count value : ℕ} (hvalue : value < 2 ^ bits)
    (j : Fin count) (x : BitString (count * bits)) :
    (supportWordFormula bits count value j).eval interpretation x =
      decide ((equivFin bits (block x j) : ℕ) = value) := by
  rw [Bool.eq_iff_iff]
  simp only [supportWordFormula, Formula.eval_andList, List.all_eq_true,
    List.forall_mem_ofFn_iff, Formula.eval_literal, beq_iff_eq, decide_eq_true_eq]
  let valueFin : Fin (2 ^ bits) := ⟨value, hvalue⟩
  constructor
  · intro h
    have hx : block x j = (equivFin bits).symm valueFin := by
      funext k
      rw [BitString.equivFin_symm_apply]
      exact h k
    have := congrArg (equivFin bits) hx
    simpa only [Equiv.apply_symm_apply, valueFin] using congrArg Fin.val this
  · intro h
    have hx : block x j = (equivFin bits).symm valueFin := by
      apply (equivFin bits).injective
      rw [Equiv.apply_symm_apply]
      exact Fin.ext h
    intro k
    change block x j k = value.testBit k.val
    rw [hx, BitString.equivFin_symm_apply]

/-- The indicator circuit returns the finite set of values represented by the corrected words. -/
theorem eval_supportIndicatorCircuit {bits n count : ℕ} (hn : n ≤ 2 ^ bits)
    (x : BitString (count * bits)) :
    (supportIndicatorCircuit bits n count).eval interpretation x =
      indicatorVector n
        ((List.ofFn fun j => (equivFin bits (block x j) : ℕ)).toFinset) := by
  funext i
  rw [Bool.eq_iff_iff]
  simp only [supportIndicatorCircuit, Circuit.eval_pi, Formula.eval_toCircuit,
    supportIndicatorFormula, Formula.eval_orList, List.any_eq_true, indicatorVector_apply,
    decide_eq_true_eq, List.mem_toFinset]
  constructor
  · rintro ⟨F, hF, hFx⟩
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hF
    rw [eval_supportWordFormula (i.isLt.trans_le hn), decide_eq_true_eq] at hFx
    exact List.mem_ofFn.mpr ⟨j, hFx⟩
  · intro hi
    obtain ⟨j, hj⟩ := List.mem_ofFn.mp hi
    refine ⟨supportWordFormula bits count i.val j, List.mem_ofFn.mpr ⟨j, rfl⟩, ?_⟩
    rw [eval_supportWordFormula (i.isLt.trans_le hn), decide_eq_true_eq]
    exact hj

/-- Compute all multiply-high candidates independently on consecutive fair-word blocks. -/
@[expose] def supportCandidateCircuit (width bits n count : ℕ) :
    Circuit signature (count * width) (count * bits) :=
  Circuit.parallelFamily fun j => candidateCircuit width bits n j.val

/-- Each candidate block is the corresponding source multiply-high value. -/
theorem val_block_eval_supportCandidateCircuit {width bits n count : ℕ}
    (hcount : count ≤ n) (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    (fun j => (equivFin bits (block
      ((supportCandidateCircuit width bits n count).eval interpretation x) j) : ℕ)) =
      fun j => j.val + (equivFin width (block x j) : ℕ) * (n - j.val) / 2 ^ width := by
  funext j
  have hblock :
      block ((supportCandidateCircuit width bits n count).eval interpretation x) j =
        (candidateCircuit width bits n j.val).eval interpretation (block x j) := by
    funext i
    exact Circuit.eval_parallelFamily_apply
      (fun j => candidateCircuit width bits n j.val) interpretation x j i
  rw [hblock]
  exact val_eval_candidateCircuit (j.isLt.trans_le hcount) hn (block x j)

/-- The complete Boolean sampler: multiply-high candidates, descending collision correction, and
the `n`-bit indicator of the corrected support. -/
@[expose] def supportSamplerCircuit (width bits n count : ℕ) :
    Circuit signature (count * width) n :=
  (supportIndicatorCircuit bits n count).comp
    ((supportScanCircuit bits 0 count).comp
      (supportCandidateCircuit width bits n count))

/-- The native Boolean circuit implements the deterministic word-array form of `SampleSupport2`. -/
theorem eval_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    (supportSamplerCircuit width bits n count).eval interpretation x =
      indicatorVector n (supportFromWords width n
        (fun j => equivFin width (block x j))) := by
  have hscan := val_eval_supportScanCircuit (bits := bits) (offset := 0) (count := count)
    (show 0 + count ≤ 2 ^ bits by omega)
    (block ((supportCandidateCircuit width bits n count).eval interpretation x))
  have hcandidates := val_block_eval_supportCandidateCircuit hcount hn x
  simp only [blocksEquiv_symm_block] at hscan
  rw [supportSamplerCircuit, Circuit.eval_comp, Circuit.eval_comp,
    eval_supportIndicatorCircuit hn.le, hscan, toFinset_scanSupport, supportFromWords,
    hcandidates]

/-- Uniform seed bits are equivalent to an independent array of bounded source words. -/
def supportSeedEquiv (width count : ℕ) :
    BitString (count * width) ≃ (Fin count → Fin (2 ^ width)) :=
  (blocksEquiv (m := count) (k := width) (α := Bool)).trans
    (Equiv.piCongrRight fun _ => equivFin width)

@[simp] theorem supportSeedEquiv_apply (width count : ℕ) (x : BitString (count * width)) :
    supportSeedEquiv width count x = fun j => equivFin width (block x j) := by
  funext j
  simp [supportSeedEquiv]

/-- Measuring the native reversible sampler gives exactly `sampleSupport2`, represented by its
`n`-bit indicator. No extra approximation or abort event is introduced. -/
theorem samplerDist_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) :
    samplerDist (supportSamplerCircuit width bits n count) =
      (ProbComp.eval (sampleSupport2 width n count)).map (indicatorVector n) := by
  rw [samplerDist_eq_outputDist, Circuit.outputDist, eval_sampleSupport2, PMF.map_comp,
    ← Probability.PMF.uniformOfFintype_map_equiv (supportSeedEquiv width count), PMF.map_comp]
  congr 1 with x : 1
  simpa only [Function.comp_apply, supportSeedEquiv_apply] using
    eval_supportSamplerCircuit hcount hn x

/-- Every Boolean and measured basis output has the requested weight; finite-width bias changes
probabilities, not the support cardinality. -/
theorem weight_eval_supportSamplerCircuit {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) (x : BitString (count * width)) :
    weight ((supportSamplerCircuit width bits n count).eval interpretation x) = count := by
  rw [eval_supportSamplerCircuit hcount hn]
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp
    (supportFromWords_mem_powersetCard hcount
      (fun j => equivFin width (block x j)))
  rw [weight_indicatorVector hsub, hcard]

/-- The measured circuit inherits the existing finite-width discrepancy bound. This is a
statistical error term, not an abort probability. -/
theorem supportSamplerDist_closeTo_ideal {width bits n count : ℕ} (hcount : count ≤ n)
    (hn : n < 2 ^ bits) :
    CloseTo (samplerDist (supportSamplerCircuit width bits n count))
      ((PMF.uniformOfFinset ((range n).powersetCard count)
        (powersetCard_nonempty.mpr (by simpa only [card_range] using hcount))).map
          (indicatorVector n))
      (ENNReal.ofReal (1 - (supportLowerDensity width n 0 count).toReal)) := by
  rw [samplerDist_supportSamplerCircuit hcount hn]
  exact (sampleSupport2_closeTo hcount).map (indicatorVector n)

/-! ### Instantiated online resources -/

/-- Active qubits are the fair seeds, all Boolean gate values, one zero, and the output block. -/
theorem supportSamplerWidth (width bits n count : ℕ) :
    samplerWidth (count * width) (supportSamplerCircuit width bits n count).code =
      count * width + (supportSamplerCircuit width bits n count).size + 1 + n :=
  samplerWidth_circuit _

/-- The reversible realization uses at most three elementary classical gates per Boolean gate,
besides one Hadamard per seed and one CNOT per output. -/
theorem length_supportSamplerCodes_le (width bits n count : ℕ) :
    (samplerCodes (count * width) (supportSamplerCircuit width bits n count).code).length ≤
      count * width + 3 * (supportSamplerCircuit width bits n count).size + n := by
  have h :=
    length_samplerCodes_le (count * width) (supportSamplerCircuit width bits n count).code
  rw [Circuit.length_code_fst] at h
  simpa only [Circuit.code, List.length_ofFn] using h

/-- The native sampler has the exact active width, the construction-derived gate budget, no
coherent oracle queries, and the full encoded description of the measured circuit. -/
theorem within_supportSamplerCodes (width bits n count : ℕ) :
    OracleCircuit.Within
      ((samplerCodes (count * width) (supportSamplerCircuit width bits n count).code).map
        fun g => OracleGateCode.gate (false, g))
      (count * width + (supportSamplerCircuit width bits n count).size + 1 + n)
      (encOracleCircuitDescription
        (samplerDescription (count * width)
          (supportSamplerCircuit width bits n count).code)).length
      ⟨count * width + (supportSamplerCircuit width bits n count).size + 1 + n,
        count * width + 3 * (supportSamplerCircuit width bits n count).size + n, 0,
        (encOracleCircuitDescription
          (samplerDescription (count * width)
            (supportSamplerCircuit width bits n count).code)).length⟩ := by
  have h := within_samplerCodes (count * width)
    (supportSamplerCircuit width bits n count).code
  rw [samplerWidth_circuit, Circuit.length_code_fst] at h
  simpa only [Circuit.code, List.length_ofFn] using h

/-- Encoded instruction length, including unary wire indices and list framing. -/
theorem length_encoding_supportSamplerCodes_le (width bits n count : ℕ) :
    (encList encGateCode
      (samplerCodes (count * width) (supportSamplerCircuit width bits n count).code)).length ≤
      (count * width + 3 * (supportSamplerCircuit width bits n count).size + n) *
        (12 * (count * width + (supportSamplerCircuit width bits n count).size + 1 + n) + 1) := by
  have h := length_encoding_samplerCodes_le (count * width)
    (supportSamplerCircuit width bits n count).code
  rw [samplerWidth_circuit, Circuit.length_code_fst] at h
  simpa only [Circuit.code, List.length_ofFn] using h

/-! ### Boundary cases -/

/-- Zero requested positions produce the all-zero indicator, with no random or abort branch. -/
theorem eval_supportSamplerCircuit_zero_count {width bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString (0 * width)) :
    (supportSamplerCircuit width bits n 0).eval interpretation x = fun _ => false := by
  rw [eval_supportSamplerCircuit (Nat.zero_le n) hn]
  funext i
  simp [supportFromWords, resolveSupport]

/-- The empty universe and empty requested support give the unique empty bit string. -/
theorem eval_supportSamplerCircuit_zero_universe (width bits : ℕ) (x : BitString 0) :
    (supportSamplerCircuit width bits 0 0).eval interpretation
      (x ∘ Fin.cast (Nat.zero_mul width)) = fun _ => false := by
  funext i
  exact i.elim0

/-- At full requested weight, every seed produces the all-one indicator of the universe. -/
theorem eval_supportSamplerCircuit_full {width bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString (n * width)) :
    (supportSamplerCircuit width bits n n).eval interpretation x = fun _ => true := by
  rw [eval_supportSamplerCircuit le_rfl hn, supportFromWords_full]
  funext i
  simp [indicatorVector]

/-- The full-support edge case remains exact with zero-bit source words. -/
theorem eval_supportSamplerCircuit_zero_width_full {bits n : ℕ} (hn : n < 2 ^ bits)
    (x : BitString 0) :
    (supportSamplerCircuit 0 bits n n).eval interpretation x = fun _ => true := by
  simpa using eval_supportSamplerCircuit_full (width := 0) hn x

end Cslib.Crypto.HQC
