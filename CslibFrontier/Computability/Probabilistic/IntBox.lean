/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.IntBinary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.Repeat
public import CslibFrontier.Computability.Probabilistic.UniformNat
public import CslibFrontier.Languages.Probabilistic.IntBox
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.PolyTime

/-!
# Strict-PPT integer-box samplers

The integer-box samplers of `CslibFrontier.Languages.Probabilistic.IntBox` run in strict
probabilistic polynomial time when the radius `B` is given in binary and the dimension `m` and bit
width `width` are given in unary. Their coin maps are deterministic polynomial-time functions of
the same inputs and the raw coin bits.

## Main results

* `Cslib.Probability.computableInPolyTime_boxShift`,
  `Cslib.Probability.computableInPolyTime_sampleModNatCoins`,
  `Cslib.Probability.computableInPolyTime_sampleIntBoxCoins`,
  `Cslib.Probability.computableInPolyTime_sampleIntBoxListCoins`,
  `Cslib.Probability.computableInPolyTime_sampleDyadicIntBoxCoins`: the coin maps.
* `Cslib.Probability.isPPTOn_sampleIntBox`, `Cslib.Probability.isPPTOn_sampleIntBoxList`,
  `Cslib.Probability.isPPTOn_sampleDyadicIntBox`: the samplers, for computed parameters.
-/

public section

namespace Cslib.Probability

open Turing.MultiTapeTM

/-- `boxShift` is computable in polynomial time on binary natural inputs. -/
@[fun_prop]
theorem computableInPolyTime_boxShift :
    ComputableInPolyTime (fun p : ℕ × ℕ => boxShift p.1 p.2)
      (encPair encNat encNat) encIntBin := by
  unfold boxShift
  fun_prop

/-- `sampleModNatCoins` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_sampleModNatCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleModNatCoins p.1 p.2)
      (encPair encNat encBits) encNat := by
  unfold sampleModNatCoins
  exact ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.bitsBinaryValue.comp (by fun_prop)) (by fun_prop)

/-- `sampleIntBoxCoins` is computable in polynomial time from a binary bound and raw coin bits. -/
@[fun_prop]
theorem computableInPolyTime_sampleIntBoxCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleIntBoxCoins p.1 p.2)
      (encPair encNat encBits) encIntBin := by
  unfold sampleIntBoxCoins
  have hmodulus : ComputableInPolyTime (fun p : ℕ × List Bool => 2 * p.1 + 1)
      (encPair encNat encBits) encNat :=
    ComputableInPolyTime.binary_add' (by fun_prop) (by fun_prop)
  apply computableInPolyTime_boxShift.comp
    (g := fun p : ℕ × List Bool => (p.1, sampleModNatCoins (2 * p.1 + 1) p.2))
  apply ComputableInPolyTime.prod
  · fun_prop
  · exact computableInPolyTime_sampleModNatCoins.comp (hmodulus.prod (by fun_prop))

/-- `sampleIntBox` is uniformly strict PPT when the radius `B` is supplied in binary and the bit
width `width` is supplied in unary. -/
theorem isPPTOn_sampleIntBox {α : Type} {input : α ↪ List Bool} {B width : α → ℕ}
    (hB : ComputableInPolyTime B input encNat)
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input encIntBin (fun a => sampleIntBox (B a) (width a)) := by
  have hmod : ComputableInPolyTime (fun a => 2 * B a + 1) input encNat :=
    ComputableInPolyTime.binary_add'
      (ComputableInPolyTime.binary_mul' (.const 2) hB) (.const 1)
  have hshift : ComputableInPolyTime (fun p : α × ℕ => boxShift (B p.1) p.2)
      (encPair input encNat) encIntBin :=
    computableInPolyTime_boxShift.comp (g := fun p : α × ℕ => (B p.1, p.2))
      ((hB.comp (.fst input encNat)).prod (.snd input encNat))
  exact (isPPTOn_sampleModNat hwidth hmod).map_with hshift

/-- `sampleIntBoxListCoins` is computable in polynomial time when `B` is in binary and `m, width`
are in unary. -/
@[fun_prop]
theorem computableInPolyTime_sampleIntBoxListCoins :
    ComputableInPolyTime
      (fun p : ℕ × ℕ × ℕ × List Bool => sampleIntBoxListCoins p.1 p.2.1 p.2.2.1 p.2.2.2)
      (encPair encNat (encPair encUnary (encPair encUnary encBits))) (encList encIntBin) := by
  unfold sampleIntBoxListCoins
  apply ComputableInPolyTime.mapWithInput
    (list := fun p : ℕ × ℕ × ℕ × List Bool => BitString.listRows p.2.1 p.2.2.1 p.2.2.2)
    (f := fun (p : ℕ × ℕ × ℕ × List Bool) row => sampleIntBoxCoins p.1 row)
  · exact ComputableInPolyTime.bitsRowsWithInput (by fun_prop) (by fun_prop) (by fun_prop)
  · exact computableInPolyTime_sampleIntBoxCoins.comp
      (g := fun q : (ℕ × ℕ × ℕ × List Bool) × List Bool => (q.1.1, q.2)) (by fun_prop)

/-- `sampleIntBoxList` is uniformly strict PPT when `B` is in binary and `m, width` are in unary. -/
theorem isPPTOn_sampleIntBoxList {α : Type} {input : α ↪ List Bool} {B m width : α → ℕ}
    (hB : ComputableInPolyTime B input encNat)
    (hm : ComputableInPolyTime m input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input (encList encIntBin) (fun a => sampleIntBoxList (B a) (m a) (width a)) :=
  (isPPTOn_sampleIntBox hB hwidth).replicate hm

/-- `sampleDyadicIntBoxCoins` is computable in polynomial time for a unary bit width. -/
@[fun_prop]
theorem computableInPolyTime_sampleDyadicIntBoxCoins :
    ComputableInPolyTime (fun p : ℕ × List Bool => sampleDyadicIntBoxCoins p.1 p.2)
      (encPair encUnary encBits) encIntBin := by
  unfold sampleDyadicIntBoxCoins
  fun_prop

/-- `sampleDyadicIntBox` is uniformly strict PPT for a unary bit width. -/
theorem isPPTOn_sampleDyadicIntBox {α : Type} {input : α ↪ List Bool} {width : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary) :
    IsPPTOn input encIntBin (fun a => sampleDyadicIntBox (width a)) := by
  have hshift : ComputableInPolyTime
      (fun p : α × ℕ => (p.2 : ℤ) - (2 : ℤ) ^ (width p.1 - 1))
      (encPair input encNat) encIntBin := by
    fun_prop
  exact (ComputableInPolyTime.sampleBinaryNat hwidth).map_with hshift

end Cslib.Probability
