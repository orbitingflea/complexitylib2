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

/-- Convert the corrected word array into the indicator of its values in `range n`. -/
@[expose] def supportIndicatorCircuit (bits n count : ℕ) :
    Circuit signature (count * bits) n :=
  Circuit.pi fun i =>
    Circuit.balanced (Circuit.oneGate (σ := signature) .or id)
      (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
      (List.ofFn fun j : Fin count =>
        Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
          (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
          (List.ofFn fun k : Fin bits =>
            (Formula.literal (fun _ => i.val.testBit k.val)
              (finProdFinEquiv (j, k))).toCircuit))

/-- The indicator circuit returns the finite set of values represented by the corrected words. -/
theorem eval_supportIndicatorCircuit {bits n count : ℕ} (hn : n ≤ 2 ^ bits)
    (x : BitString (count * bits)) :
    (supportIndicatorCircuit bits n count).eval interpretation x =
      indicatorVector n
        ((List.ofFn fun j => (equivFin bits (block x j) : ℕ)).toFinset) := by
  funext i
  simp only [supportIndicatorCircuit, Circuit.eval_pi]
  have foldr_and_eq_all (l : List Bool) : l.foldr (· && ·) true = l.all id := by
    induction l <;> simp_all
  have foldr_or_eq_any (l : List Bool) : l.foldr (· || ·) false = l.any id := by
    induction l <;> simp_all
  have hword (j : Fin count) :
      (Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
        (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
        (List.ofFn fun k : Fin bits =>
          (Formula.literal (fun _ => i.val.testBit k.val)
            (finProdFinEquiv (j, k))).toCircuit)).eval interpretation x 0 =
        decide ((equivFin bits (block x j) : ℕ) = i.val) := by
    rw [Circuit.eval_balanced]
    rw [List.balancedFold_hom (g := fun y : Fin 1 → Bool => y 0)
      (op' := (· && ·)) (fun _ _ => rfl)]
    simp only [Fin.isValue, Circuit.eval_oneGate, Boolean.interpretation]
    rw [List.balancedFold_eq_foldr, foldr_and_eq_all]
    have hleaf (k : Fin bits) :
        ((((fun y : Fin 1 → Bool => y 0) ∘ fun C => C.eval interpretation x) ∘
          fun k : Fin bits => (Formula.literal (fun _ => i.val.testBit k.val)
            (finProdFinEquiv (j, k))).toCircuit) k) =
          (x (finProdFinEquiv (j, k)) == i.val.testBit k.val) := by
      simp only [Function.comp_apply]
      rw [Formula.eval_toCircuit, Formula.eval_literal]
    rw [Bool.eq_iff_iff]
    simp only [List.map_ofFn, List.all_eq_true, List.forall_mem_ofFn_iff, id_eq,
      decide_eq_true_eq]
    let valueFin : Fin (2 ^ bits) := ⟨i, i.isLt.trans_le hn⟩
    constructor
    · intro h
      have hx : block x j = (equivFin bits).symm valueFin := by
        funext k
        rw [BitString.equivFin_symm_apply]
        have hk := h k
        rw [hleaf] at hk
        exact beq_iff_eq.mp hk
      have := congrArg (equivFin bits) hx
      simpa only [Equiv.apply_symm_apply, valueFin] using congrArg Fin.val this
    · intro h
      have hx : block x j = (equivFin bits).symm valueFin := by
        apply (equivFin bits).injective
        rw [Equiv.apply_symm_apply]
        exact Fin.ext h
      intro k
      rw [hleaf]
      change (block x j k == i.val.testBit k.val) = true
      rw [hx, BitString.equivFin_symm_apply]
      simp [valueFin]
  rw [Circuit.eval_balanced]
  rw [List.balancedFold_hom (g := fun y : Fin 1 → Bool => y 0)
    (op' := (· || ·)) (fun _ _ => rfl)]
  simp only [Fin.isValue, Circuit.eval_oneGate, Boolean.interpretation, Nat.reduceAdd,
    indicatorVector_apply, List.mem_toFinset, List.mem_ofFn]
  rw [List.balancedFold_eq_foldr, foldr_or_eq_any]
  have hvalue (j : Fin count) :
      ((((fun y : Fin 1 → Bool => y 0) ∘ fun C => C.eval interpretation x) ∘
        fun j : Fin count =>
          Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
            (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
            (List.ofFn fun k : Fin bits =>
              (Formula.literal (fun _ => i.val.testBit k.val)
                (finProdFinEquiv (j, k))).toCircuit)) j) =
        decide ((equivFin bits (block x j) : ℕ) = i.val) := by
    simpa only [Function.comp_apply] using hword j
  have hvalues :
      List.ofFn ((((fun y : Fin 1 → Bool => y 0) ∘ fun C => C.eval interpretation x) ∘
        fun j : Fin count =>
          Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
            (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
            (List.ofFn fun k : Fin bits =>
              (Formula.literal (fun _ => i.val.testBit k.val)
                (finProdFinEquiv (j, k))).toCircuit))) =
        List.ofFn (fun j : Fin count =>
          decide ((equivFin bits (block x j) : ℕ) = i.val)) := by
    exact congrArg List.ofFn (funext hvalue)
  rw [List.map_ofFn, hvalues]
  rw [Bool.eq_iff_iff]
  simp

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
