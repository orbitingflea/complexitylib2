/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.PolyTime
import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Collision.PolyTime
import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve
import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Sampler
public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Resources
import CslibFrontier.Foundations.Data.BitString.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Mathlib.Data.Fin.VecNotation

/-! Concrete native generation, nonconstant reversible execution, and candidate boundary cases. -/

public section

namespace CslibFrontierTests.HQCSupportCircuit

open Cslib Cslib.Crypto.HQC Cslib.Circuits Cslib.Circuits.Boolean Cslib.Quantum
open Finset Probability BitString
open Turing.MultiTapeTM ComputableInPolyTime

private def candidateBit (width : ℕ) : Circuits.Circuit signature width 1 :=
  (Circuits.Circuit.wiring signature (fun _ : Fin 1 => (0 : Fin 3))).comp
    (candidateCircuit width 3 5 1)

private theorem candidateBit_polyTime :
    ComputableInPolyTime (fun width => (candidateBit width).code) encUnary encCode := by
  have h := computableInPolyTime_compCode unary_to_binary
    (const (Circuits.Circuit.wiring signature (fun _ : Fin 1 => (0 : Fin 3))).code)
    (computableInPolyTime_candidateCircuit id' (const 3) (const 5) (const 1))
  simpa only [candidateBit, compCode_code] using h

def candidateFamily : UniformCircuitFamily :=
  .ofBooleanCircuits candidateBit candidateBit_polyTime

private theorem candidateFamily_accept (x : List Bool) :
    candidateFamily.acceptProb x =
      if (1 + (BitString.equivFin x.length (fun i => x[i]) : ℕ) * 4 / 2 ^ x.length).testBit 0
      then 1 else 0 := by
  rw [candidateFamily, UniformCircuitFamily.acceptProb_ofBooleanCircuits]
  simp only [candidateBit, Circuits.Circuit.eval_comp, Circuits.Circuit.eval_wiring,
    Function.comp_apply]
  rw [← BitString.testBit_equivFin
    ((candidateCircuit x.length 3 5 1).eval interpretation (fun i => x[i])) (0 : Fin 3),
    val_eval_candidateCircuit (by decide : 1 < 5) (by decide : 5 < 2 ^ 3)]
  rfl

-- Actual compiled quantum execution distinguishes two different fair-word inputs.
example : candidateFamily.acceptProb [false, false] = 1 := by
  rw [candidateFamily_accept]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_two]
  decide

example : candidateFamily.acceptProb [true, false] = 0 := by
  rw [candidateFamily_accept]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_two]
  decide

-- The first shrinking interval can have three elements, so this is not dyadic reduction.
example : (BitString.equivFin 2 ((candidateCircuit 2 2 3 0).eval interpretation ![true, true]) : ℕ)
    = 2 := by
  rw [val_eval_candidateCircuit (by decide) (by decide)]
  norm_num [BitString.val_equivFin_eq_sum, Fin.sum_univ_succ]

-- A zero-bit random word gives the lower endpoint, without abort or an uncharged random draw.
example : (BitString.equivFin 3 ((candidateCircuit 0 3 5 2).eval interpretation Fin.elim0) : ℕ)
    = 2 := by
  rw [val_eval_candidateCircuit (by decide) (by decide)]
  norm_num [BitString.val_equivFin_eq_sum]

-- Raw generation remains total for invalid intervals and empty outputs.
example : (candidateCode 0 0 0 1).2 = [] := by decide

example (width : ℕ) : (candidateBit width).size ≤
    63 * (width + 4) ^ 2 + 342 := by
  have h := size_candidateCircuit_le width 3 5 1
  simpa [candidateBit, Nat.add_assoc] using h

-- A collision replaces the current word, while a different later word leaves it alone.
example : (collisionStepCircuit 2 1).eval interpretation
    (Fin.append ![false, true] ![false, true]) = ![true, false] := by
  rw [eval_collisionStepCircuit]
  decide

example : (collisionStepCircuit 2 1).eval interpretation
    (Fin.append ![false, true] ![true, true]) = ![false, true] := by
  rw [eval_collisionStepCircuit]
  decide

example : (collisionStepCode 0 7).2 = [] := by decide

example (bits offset : ℕ) :
    (collisionStepCircuit bits offset).size = 13 * bits + 6 :=
  size_collisionStepCircuit bits offset

example : ComputableInPolyTime
    (fun p : ℕ × ℕ => (collisionStepCircuit p.1 p.2).code)
    (encPair encUnary encUnary) encCode :=
  computableInPolyTime_collisionStepCircuit (fst _ _) (snd _ _)

-- After a collision, later comparisons retain the replacement and leave the suffix intact.
example : (collisionScanCircuit 2 0 2 [0, 1]).eval interpretation
    (Fin.append ![true, true] (BitString.blocksEquiv.symm ![![true, true], ![true, false]])) =
      Fin.append ![false, false] (BitString.blocksEquiv.symm ![![true, true], ![true, false]]) := by
  rw [eval_collisionScanCircuit]
  decide

example (bits offset count : ℕ) :
    (collisionScanCircuit bits offset count (List.finRange count)).size =
      count * (13 * bits + 6) := by
  rw [size_collisionScanCircuit, List.length_finRange]

-- The head must scan the corrected suffix: raw candidates [1, 2, 2] become [0, 1, 2].
-- Comparing the head against only the original suffix would incorrectly retain 1.
example : (fun j => (BitString.equivFin 2 (BitString.block
    ((supportScanCircuit 2 0 3).eval interpretation
      (BitString.blocksEquiv.symm ![![true, false], ![false, true], ![false, true]])) j) : ℕ)) =
      ![0, 1, 2] := by
  rw [val_eval_supportScanCircuit (by decide)]
  decide

example (bits offset : ℕ) : (supportScanCircuit bits offset 0).size = 0 := by
  rw [size_supportScanCircuit]
  simp

example : (supportScanCircuit 0 0 2).size = 6 := by
  rw [size_supportScanCircuit]
  decide

-- A small non-dyadic specialization with two one-bit words and two-bit corrected positions.
private def nonDyadicSupportCircuit : Circuits.Circuit signature 2 3 :=
  supportSamplerCircuit 1 2 3 2

-- Words producing the duplicate nonzero raw candidate array `(1, 1)`.
private def nonDyadicCollisionWords : Fin 2 → Fin 2 := fun j => if j = 0 then 1 else 0

-- The corresponding two fair seed bits.
private def nonDyadicCollisionSeed : BitString 2 :=
  blocksEquiv.symm fun j => (equivFin 1).symm (nonDyadicCollisionWords j)

-- Both source candidate formulas return the nonzero value `1`.
example :
    (fun j : Fin 2 => j.val + (nonDyadicCollisionWords j).val * (3 - j.val) / 2 ^ 1) =
      fun _ => 1 := by
  decide

-- The descending collision rule replaces the first duplicate `1` by its offset `0`.
private theorem supportFromWords_nonDyadicCollision :
    supportFromWords 1 3 nonDyadicCollisionWords = {0, 1} := by
  decide

-- The concrete circuit exposes that correction in its fixed-weight output support.
example :
    nonDyadicSupportCircuit.eval interpretation nonDyadicCollisionSeed =
      indicatorVector 3 {0, 1} := by
  rw [nonDyadicSupportCircuit, eval_supportSamplerCircuit (by decide) (by decide)]
  have hseed : (fun j => equivFin 1 (block nonDyadicCollisionSeed j)) =
      nonDyadicCollisionWords := by
    funext j
    change equivFin 1
      (block (blocksEquiv.symm fun j => (equivFin 1).symm (nonDyadicCollisionWords j)) j) = _
    rw [congrFun (block_blocksEquiv_symm _) j, Equiv.apply_symm_apply]
  rw [hseed, supportFromWords_nonDyadicCollision]

-- The complete native sampler has the implemented support law and its separate resource bounds.
example :
    Reversible.samplerDist nonDyadicSupportCircuit =
      (ProbComp.eval (sampleSupport2 1 3 2)).map (indicatorVector 3) := by
  simpa only [nonDyadicSupportCircuit] using
    samplerDist_supportSamplerCircuit (width := 1) (bits := 2) (n := 3) (count := 2)
      (by decide) (by decide)

example :
    CloseTo (Reversible.samplerDist nonDyadicSupportCircuit)
      ((PMF.uniformOfFinset ((range 3).powersetCard 2)
        (powersetCard_nonempty.mpr (by decide))).map (indicatorVector 3))
      (ENNReal.ofReal (1 - (supportLowerDensity 1 3 0 2).toReal)) := by
  simpa only [nonDyadicSupportCircuit] using
    supportSamplerDist_closeTo_ideal (width := 1) (bits := 2) (n := 3) (count := 2)
      (by decide) (by decide)

example (x : BitString 2) :
    weight (nonDyadicSupportCircuit.eval interpretation x) = 2 := by
  simpa only [nonDyadicSupportCircuit] using
    weight_eval_supportSamplerCircuit (width := 1) (bits := 2) (n := 3) (count := 2)
      (by decide) (by decide) x

example :
    Reversible.samplerWidth 2 nonDyadicSupportCircuit.code =
      2 + nonDyadicSupportCircuit.size + 1 + 3 := by
  simpa only [nonDyadicSupportCircuit] using supportSamplerWidth 1 2 3 2

example :
    (Reversible.samplerCodes 2 nonDyadicSupportCircuit.code).length ≤
      2 + 3 * nonDyadicSupportCircuit.size + 3 := by
  simpa only [nonDyadicSupportCircuit] using length_supportSamplerCodes_le 1 2 3 2

example :
    OracleCircuit.Within
      ((Reversible.samplerCodes 2 nonDyadicSupportCircuit.code).map
        fun g => OracleGateCode.gate (false, g))
      (2 + nonDyadicSupportCircuit.size + 1 + 3)
      ⟨2 + nonDyadicSupportCircuit.size + 1 + 3,
        2 + 3 * nonDyadicSupportCircuit.size + 3, 0⟩ := by
  simpa only [nonDyadicSupportCircuit] using within_supportSamplerCodes 1 2 3 2

example :
    (encList encGateCode (Reversible.samplerCodes 2 nonDyadicSupportCircuit.code)).length ≤
      (2 + 3 * nonDyadicSupportCircuit.size + 3) *
        (12 * (2 + nonDyadicSupportCircuit.size + 1 + 3) + 1) := by
  simpa only [nonDyadicSupportCircuit] using length_encoding_supportSamplerCodes_le 1 2 3 2

end CslibFrontierTests.HQCSupportCircuit
