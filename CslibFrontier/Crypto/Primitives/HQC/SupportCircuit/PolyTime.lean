/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.BalancedCode
public import CslibFrontier.Computability.Circuit.Boolean.ParallelCode
public import CslibFrontier.Computability.Circuit.Boolean.Modular.Multiply.PolyTime
public import CslibFrontier.Computability.Circuit.Boolean.WordConstant.PolyTime
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Resolve.PolyTime
public import CslibFrontier.Crypto.Primitives.HQC.SupportCircuit.Sampler
import CslibFrontier.Computability.Circuit.Boolean.CarryLookahead.PolyTime
import CslibFrontier.Computability.Circuit.Boolean.EncodingSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Lookup

/-!
# Native generation of the HQC support-sampler circuit

Raw code construction uses existing sequential and parallel composition, including every
constant, widened multiplier input, output selector and addition gate.

## Main definitions

* `Cslib.Crypto.HQC.candidateCode`: total native code generation for a candidate.

## Main results

* `Cslib.Crypto.HQC.candidateCode_eq_code`: exact agreement with the typed circuit.
* `Cslib.Crypto.HQC.computableInPolyTime_candidateCircuit`: generation from unary parameters.

These are original compiler certificates for the existing candidate formula. They do not charge
an offline compiler as attack execution or assert a static generator-description size.
-/

public section

namespace Cslib.Crypto.HQC

open Circuits Circuits.Boolean Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Emit all gates and output references of the concrete candidate circuit. -/
@[expose] def candidateCode (width bits n offset : ℕ) : List (Op × List ℕ) × List ℕ :=
  compCode width (carryLookaheadAdd bits).code
    (appendCode width
      (compCode width ([], (List.range bits).map (width + ·))
        (compCode width (Modular.multiply (width + bits)).code
          (appendCode width
            (appendCode width ([], List.range width) (wordConstCode width bits 0))
            (wordConstCode width (width + bits) (n - offset)))))
      (wordConstCode width bits offset))

/-- The emitted raw instructions agree exactly, including zero widths and invalid intervals. -/
theorem candidateCode_eq_code (width bits n offset : ℕ) :
    candidateCode width bits n offset = (candidateCircuit width bits n offset).code := by
  have hh : (Circuit.wiring signature (Fin.natAdd width : Fin bits → Fin (width + bits))).code =
      ([], (List.range bits).map (width + ·)) := Circuit.code_wiring_eq_map fun _ => rfl
  have hi : (Circuit.id signature width).code = ([], List.range width) :=
    Circuit.code_wiring_id
  rw [candidateCode, ← hh, ← hi]
  simp only [wordConstCode_eq_bits, Nat.zero_testBit, appendCode_code, compCode_code]
  rfl

private def supportLiteralCode (inputCount wire : ℕ) (expected : Bool) : Code :=
  if expected then ([], [wire]) else ([(.not, [wire])], [inputCount])

private theorem supportLiteralCode_eq_code {bits n count : ℕ} (i : Fin n) (j : Fin count)
    (k : Fin bits) :
    supportLiteralCode (count * bits) (k.val + bits * j.val) (i.val.testBit k.val) =
      (Formula.literal (fun _ => i.val.testBit k.val)
        (finProdFinEquiv (j, k))).toCircuit.code := by
  unfold supportLiteralCode Formula.literal
  split <;> rfl

private def supportWordCode (bits count value word : ℕ) : Code :=
  balancedCode (count * bits)
    (Circuit.oneGate (σ := signature) .and id).code
    (Circuit.oneGate (σ := signature) (n := count * bits) (.const true) Fin.elim0).code
    ((List.range bits).map fun k =>
      supportLiteralCode (count * bits) (k + bits * word) (value.testBit k))

private theorem supportWordCode_eq_code {bits n count : ℕ} (i : Fin n) (j : Fin count) :
    supportWordCode bits count i.val j.val =
      (Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
        (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
        (List.ofFn fun k : Fin bits =>
          (Formula.literal (fun _ => i.val.testBit k.val)
            (finProdFinEquiv (j, k))).toCircuit)).code := by
  rw [supportWordCode, List.map_range_eq_ofFn]
  rw [show (List.ofFn fun k : Fin bits =>
      supportLiteralCode (count * bits) (k.val + bits * j.val) (i.val.testBit k.val)) =
      (List.ofFn fun k : Fin bits =>
        (Formula.literal (fun _ => i.val.testBit k.val)
          (finProdFinEquiv (j, k))).toCircuit).map Circuit.code by
    rw [List.map_ofFn]
    congr 1
    funext k
    exact supportLiteralCode_eq_code i j k]
  exact balancedCode_eq_code _ _ _

private def supportValueCode (bits count value : ℕ) : Code :=
  balancedCode (count * bits)
    (Circuit.oneGate (σ := signature) .or id).code
    (Circuit.oneGate (σ := signature) (n := count * bits) (.const false) Fin.elim0).code
    ((List.range count).map fun j => supportWordCode bits count value j)

private theorem supportValueCode_eq_code {bits n count : ℕ} (i : Fin n) :
    supportValueCode bits count i.val =
      (Circuit.balanced (Circuit.oneGate (σ := signature) .or id)
        (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
        (List.ofFn fun j : Fin count =>
          Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
            (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
            (List.ofFn fun k : Fin bits =>
              (Formula.literal (fun _ => i.val.testBit k.val)
                (finProdFinEquiv (j, k))).toCircuit))).code := by
  rw [supportValueCode, List.map_range_eq_ofFn]
  rw [show (List.ofFn fun j : Fin count => supportWordCode bits count i.val j.val) =
      (List.ofFn fun j : Fin count =>
        Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
          (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
          (List.ofFn fun k : Fin bits =>
            (Formula.literal (fun _ => i.val.testBit k.val)
              (finProdFinEquiv (j, k))).toCircuit)).map Circuit.code by
    rw [List.map_ofFn]
    congr 1
    funext j
    exact supportWordCode_eq_code i j]
  exact balancedCode_eq_code _ _ _

/-- Emit the complete `n`-bit membership indicator of a corrected `count`-word array. -/
@[expose] def supportIndicatorCode (bits n count : ℕ) : Code :=
  private_decl% (appendCodes (count * bits)
    ((List.range n).map fun i => supportValueCode bits count i))

/-- The native indicator compiler agrees with every gate and output reference of the typed
circuit, for arbitrary dimensions including zero. -/
theorem supportIndicatorCode_eq_code (bits n count : ℕ) :
    supportIndicatorCode bits n count = (supportIndicatorCircuit bits n count).code := by
  change appendCodes (count * bits)
    ((List.range n).map fun i => supportValueCode bits count i) = _
  rw [List.map_range_eq_ofFn]
  rw [show (List.ofFn fun i : Fin n => supportValueCode bits count i.val) =
      (List.ofFn fun i : Fin n =>
        Circuit.balanced (Circuit.oneGate (σ := signature) .or id)
          (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
          (List.ofFn fun j : Fin count =>
            Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
              (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
              (List.ofFn fun k : Fin bits =>
                (Formula.literal (fun _ => i.val.testBit k.val)
                  (finProdFinEquiv (j, k))).toCircuit))).map Circuit.code by
    rw [List.map_ofFn]
    congr 1
    funext i
    exact supportValueCode_eq_code i]
  rw [List.map_ofFn]
  simpa only [Function.comp_def, supportIndicatorCircuit] using
    (appendCodes_code (fun i : Fin n =>
      Circuit.balanced (Circuit.oneGate (σ := signature) .or id)
        (Circuit.oneGate (σ := signature) (.const false) Fin.elim0)
        (List.ofFn fun j : Fin count =>
          Circuit.balanced (Circuit.oneGate (σ := signature) .and id)
            (Circuit.oneGate (σ := signature) (.const true) Fin.elim0)
            (List.ofFn fun k : Fin bits =>
              (Formula.literal (fun _ => i.val.testBit k.val)
                (finProdFinEquiv (j, k))).toCircuit))))

/-- Emit all multiply-high candidates on consecutive independent source-word blocks. -/
@[expose] def supportCandidateCode (width bits n count : ℕ) : Code :=
  parallelFamilyCode width bits
    ((List.range count).map fun j => candidateCode width bits n j)

/-- The generic candidate-family compiler agrees exactly with `supportCandidateCircuit`. -/
theorem supportCandidateCode_eq_code (width bits n count : ℕ) :
    supportCandidateCode width bits n count =
      (supportCandidateCircuit width bits n count).code := by
  rw [supportCandidateCode, List.map_range_eq_ofFn]
  simp only [candidateCode_eq_code]
  exact parallelFamilyCode_code _

/-- Emit the candidates, descending collision correction, and membership indicator of the
complete finite HQC support sampler. -/
@[expose] def supportSamplerCode (width bits n count : ℕ) : Code :=
  compCode (count * width) (supportIndicatorCode bits n count)
    (compCode (count * width) (supportScanCode bits 0 count)
      (supportCandidateCode width bits n count))

/-- The native sampler compiler agrees exactly with the typed circuit at every finite parameter,
without imposing the semantic support bounds. -/
theorem supportSamplerCode_eq_code (width bits n count : ℕ) :
    supportSamplerCode width bits n count =
      (supportSamplerCircuit width bits n count).code := by
  rw [supportSamplerCode, supportIndicatorCode_eq_code, supportScanCode_eq_code,
    supportCandidateCode_eq_code, compCode_code, compCode_code]
  rfl

private theorem computableInPolyTime_supportLiteralCode {α : Type} {enc : α ↪ List Bool}
    {inputCount wire : α → ℕ} {expected : α → Bool}
    (hinput : ComputableInPolyTime inputCount enc encNat)
    (hwire : ComputableInPolyTime wire enc encNat)
    (hexpected : ComputableInPolyTime expected enc encBool) :
    ComputableInPolyTime
      (fun a => supportLiteralCode (inputCount a) (wire a) (expected a)) enc encCode := by
  unfold supportLiteralCode
  fun_prop

private theorem computableInPolyTime_constGateCode {α : Type} {enc : α ↪ List Bool}
    {inputCount : α → ℕ} (b : Bool)
    (hinput : ComputableInPolyTime inputCount enc encNat) :
    ComputableInPolyTime
      (fun a => (Circuit.oneGate (σ := signature) (n := inputCount a)
        (.const b) Fin.elim0).code) enc encCode :=
  (const [(Op.const b, [])]).prod (hinput.cons' (const []))

private theorem computableInPolyTime_supportWordCode {α : Type} {enc : α ↪ List Bool}
    {bits count : α → ℕ} {value word : α → ℕ}
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary)
    (hvalue : ComputableInPolyTime value enc encNat)
    (hword : ComputableInPolyTime word enc encNat) :
    ComputableInPolyTime
      (fun a => supportWordCode (bits a) (count a) (value a) (word a)) enc encCode := by
  have hinput : ComputableInPolyTime (fun a => count a * bits a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hleaves : ComputableInPolyTime
      (fun a => (List.range (bits a)).map fun k =>
        supportLiteralCode (count a * bits a) (k + bits a * word a)
          ((value a).testBit k)) enc (encList encCode) := by
    apply mapWithInput (range.comp hbits)
    have hpar := fst enc encUnary
    have hindex := unary_to_binary.comp (snd enc encUnary)
    exact computableInPolyTime_supportLiteralCode
      (hinput.comp hpar)
      (binary_add' hindex
        (binary_mul' (unary_to_binary.comp (hbits.comp hpar)) (hword.comp hpar)))
      (binary_testBit (hvalue.comp hpar) (snd enc encUnary))
  have hunit := computableInPolyTime_constGateCode true hinput
  exact computableInPolyTime_balancedCode hinput
    (const (Circuit.oneGate (σ := signature) .and id).code)
    hunit hleaves

private theorem computableInPolyTime_supportValueCode {α : Type} {enc : α ↪ List Bool}
    {bits count : α → ℕ} {value : α → ℕ}
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary)
    (hvalue : ComputableInPolyTime value enc encNat) :
    ComputableInPolyTime
      (fun a => supportValueCode (bits a) (count a) (value a)) enc encCode := by
  have hinput : ComputableInPolyTime (fun a => count a * bits a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hleaves : ComputableInPolyTime
      (fun a => (List.range (count a)).map fun j =>
        supportWordCode (bits a) (count a) (value a) j) enc (encList encCode) := by
    apply mapWithInput (range.comp hcount)
    have hpar := fst enc encUnary
    exact computableInPolyTime_supportWordCode (hbits.comp hpar) (hcount.comp hpar)
      (hvalue.comp hpar) (unary_to_binary.comp (snd enc encUnary))
  have hunit := computableInPolyTime_constGateCode false hinput
  exact computableInPolyTime_balancedCode hinput
    (const (Circuit.oneGate (σ := signature) .or id).code)
    hunit hleaves

/-- Native uniform generation of the complete support-membership indicator from unary
dimensions. -/
@[fun_prop] theorem computableInPolyTime_supportIndicatorCircuit {α : Type}
    {enc : α ↪ List Bool} {bits n count : α → ℕ}
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime
      (fun a => (supportIndicatorCircuit (bits a) (n a) (count a)).code) enc encCode := by
  have hinput : ComputableInPolyTime (fun a => count a * bits a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hvalues : ComputableInPolyTime
      (fun a => (List.range (n a)).map fun i =>
        supportValueCode (bits a) (count a) i) enc (encList encCode) := by
    apply mapWithInput (range.comp hn)
    have hpar := fst enc encUnary
    exact computableInPolyTime_supportValueCode (hbits.comp hpar) (hcount.comp hpar)
      (unary_to_binary.comp (snd enc encUnary))
  have hcode := computableInPolyTime_appendCodes hinput hvalues
  change ComputableInPolyTime
    (fun a => supportIndicatorCode (bits a) (n a) (count a)) enc encCode at hcode
  simpa only [supportIndicatorCode_eq_code] using hcode

/-- Native uniform generation of the complete candidate circuit from unary parameters.
The separate gate bound is `size_candidateCircuit_le`. -/
@[fun_prop] theorem computableInPolyTime_candidateCircuit {α : Type} {enc : α ↪ List Bool}
    {width bits n offset : α → ℕ} (hw : ComputableInPolyTime width enc encUnary)
    (hb : ComputableInPolyTime bits enc encUnary) (hn : ComputableInPolyTime n enc encUnary)
    (ho : ComputableInPolyTime offset enc encUnary) :
    ComputableInPolyTime (fun a => (candidateCircuit (width a) (bits a) (n a) (offset a)).code)
      enc encCode := by
  have hw' := unary_to_binary.comp hw
  have hwide : ComputableInPolyTime (fun a => width a + bits a) enc encUnary := by fun_prop
  have hid : ComputableInPolyTime (fun a => ([], List.range (width a))) enc encCode := by
    have h := unary_to_binary.map.comp (range.comp hw)
    simpa only [Function.comp_def, List.map_id_fun', id_eq] using
      (const (encOut := encList encGate) []).prod h
  have hhigh : ComputableInPolyTime
      (fun a => ([], (List.range (bits a)).map (width a + ·))) enc encCode := by
    have hi : ComputableInPolyTime (fun p : α × ℕ => width p.1 + p.2)
        (encPair enc encUnary) encNat := unary_to_binary.comp (by fun_prop)
    exact (const (encOut := encList encGate) []).prod (mapWithInput (range.comp hb) hi)
  have hdiff : ComputableInPolyTime (fun a => n a - offset a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have h := computableInPolyTime_compCode hw'
    (computableInPolyTime_carryLookaheadAdd.comp hb)
    (computableInPolyTime_appendCode hw'
      (computableInPolyTime_compCode hw' hhigh
        (computableInPolyTime_compCode hw' (Modular.computableInPolyTime_multiply.comp hwide)
          (computableInPolyTime_appendCode hw'
            (computableInPolyTime_appendCode hw' hid
              (computableInPolyTime_wordConstCode hw' hb (const 0)))
            (computableInPolyTime_wordConstCode hw' hwide hdiff))))
      (computableInPolyTime_wordConstCode hw' hb (unary_to_binary.comp ho)))
  change ComputableInPolyTime (fun a => candidateCode (width a) (bits a) (n a) (offset a))
    enc encCode at h
  simpa only [candidateCode_eq_code] using h

private theorem supportCandidateFold_prefix (width bits n count i : ℕ)
    (hi : i ≤ ((List.range count).map fun j => candidateCode width bits n j).length) :
    ((((List.range count).map fun j => candidateCode width bits n j).take i).foldl
      (parallelFamilyCodeStep (width, bits)) (0, ([], []))) =
        (i, (supportCandidateCircuit width bits n i).code) := by
  have hi' : i ≤ count := by simpa only [List.length_map, List.length_range] using hi
  rw [← List.map_take, List.take_range, Nat.min_eq_left hi']
  have hcodes :
      (List.range i).map (fun j => candidateCode width bits n j) =
        List.ofFn (fun j : Fin i => (candidateCircuit width bits n j.val).code) := by
    rw [List.map_range_eq_ofFn]
    simp only [candidateCode_eq_code]
  rw [hcodes]
  exact foldl_parallelFamilyCodeStep_code _

private def supportCandidateGateBound (width bits count : ℕ) : ℕ :=
  count * (63 * (width + bits + 1) ^ 2 + 21 * (bits + 1) ^ 2 + 6)

private def supportCandidateCodeBound (width bits count : ℕ) : ℕ :=
  let N := count * width
  let M := count * bits
  let G := supportCandidateGateBound width bits count
  2 * G * (23 + 8 * (N + G)) + 1 + M * (2 * (N + G) + 1)

private def supportCandidateStateBound (width bits count : ℕ) : ℕ :=
  2 * count + 1 + supportCandidateCodeBound width bits count

private theorem polyBounded_supportCandidateStateBound {α : Type} {enc : α ↪ List Bool}
    {width bits count : α → ℕ}
    (hwidth : ComputableInPolyTime width enc encUnary)
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary) :
    PolyBounded (fun a => (enc a).length)
      (fun a => supportCandidateStateBound (width a) (bits a) (count a)) := by
  have hw := hwidth.tidy.polyBounded
  have hb := hbits.tidy.polyBounded
  have hc := hcount.tidy.polyBounded
  have hsum := (hw.add hb).add (PolyBounded.const 1)
  have hgate := (((PolyBounded.const 63).mul (hsum.mul hsum)).add
    ((PolyBounded.const 21).mul ((hb.add (.const 1)).mul (hb.add (.const 1))))).add
      (.const 6)
  have hG := hc.mul hgate
  have hN := hc.mul hw
  have hM := hc.mul hb
  have hNG := hN.add hG
  have hcode := ((((PolyBounded.const 2).mul hG).mul
    ((PolyBounded.const 23).add ((PolyBounded.const 8).mul hNG))).add (.const 1)).add
      (hM.mul (((PolyBounded.const 2).mul hNG).add (.const 1)))
  have hstate := (((PolyBounded.const 2).mul hc).add (.const 1)).add hcode
  simpa [supportCandidateStateBound, supportCandidateCodeBound,
    supportCandidateGateBound, pow_two] using hstate

private theorem length_supportCandidateFold_le (width bits n count i : ℕ)
    (hi : i ≤ ((List.range count).map fun j => candidateCode width bits n j).length) :
    (encPair encUnary encCode
      ((((List.range count).map fun j => candidateCode width bits n j).take i).foldl
        (parallelFamilyCodeStep (width, bits)) (0, ([], [])))).length ≤
      supportCandidateStateBound width bits count := by
  have hi' : i ≤ count := by simpa only [List.length_map, List.length_range] using hi
  rw [supportCandidateFold_prefix width bits n count i hi]
  let B := 63 * (width + bits + 1) ^ 2 + 21 * (bits + 1) ^ 2 + 6
  have hsize : (supportCandidateCircuit width bits n i).size ≤ count * B := by
    rw [supportCandidateCircuit, Circuit.size_parallelFamily]
    calc
      ∑ j : Fin i, (candidateCircuit width bits n j.val).size ≤ ∑ _ : Fin i, B := by
        gcongr with j
        exact size_candidateCircuit_le width bits n j.val
      _ = i * B := by simp
      _ ≤ count * B := Nat.mul_le_mul_right B hi'
  have hcode := length_encCode_le (supportCandidateCircuit width bits n i)
  have hcode' :
      (encCode (supportCandidateCircuit width bits n i).code).length ≤
        supportCandidateCodeBound width bits count := hcode.trans (by
    dsimp only [supportCandidateCodeBound, supportCandidateGateBound, B]
    gcongr)
  rw [length_encPair, encUnary_apply, List.length_replicate]
  exact Nat.add_le_add (by omega) hcode'

/-- Native uniform generation of an arbitrary finite family of multiply-high candidates from
unary dimensions. The bounded fold charges the complete encoded prefix circuit. -/
@[fun_prop] theorem computableInPolyTime_supportCandidateCircuit {α : Type}
    {enc : α ↪ List Bool} {width bits n count : α → ℕ}
    (hwidth : ComputableInPolyTime width enc encUnary)
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime
      (fun a => (supportCandidateCircuit (width a) (bits a) (n a) (count a)).code)
      enc encCode := by
  let parEnc := encPair encUnary encUnary
  let stateEnc := encPair encUnary encCode
  have hlist : ComputableInPolyTime
      (fun a => (List.range (count a)).map fun j =>
        candidateCode (width a) (bits a) (n a) j) enc (encList encCode) := by
    apply mapWithInput (range.comp hcount)
    have hpar := fst enc encUnary
    have hcandidate := computableInPolyTime_candidateCircuit
      (hwidth.comp hpar) (hbits.comp hpar) (hn.comp hpar) (snd enc encUnary)
    simpa only [candidateCode_eq_code, Function.comp_def] using hcandidate
  have hfold := foldlWith (step := parallelFamilyCodeStep)
    (hwidth.prod hbits) hlist
    (const (encOut := stateEnc) ((0, ([], [])) : ℕ × Code))
    (by simpa only [parEnc, stateEnc] using computableInPolyTime_parallelFamilyCodeStep)
    (polyBounded_supportCandidateStateBound hwidth hbits hcount) fun a i hi =>
      length_supportCandidateFold_le (width a) (bits a) (n a) (count a) i hi
  have hcode := hfold.snd'
  change ComputableInPolyTime
    (fun a => supportCandidateCode (width a) (bits a) (n a) (count a)) enc encCode at hcode
  simpa only [supportCandidateCode_eq_code] using hcode

/-- Native uniform generation of the complete support sampler from arbitrary unary parameter
schedules. -/
@[fun_prop] theorem computableInPolyTime_supportSamplerCircuit {α : Type}
    {enc : α ↪ List Bool} {width bits n count : α → ℕ}
    (hwidth : ComputableInPolyTime width enc encUnary)
    (hbits : ComputableInPolyTime bits enc encUnary)
    (hn : ComputableInPolyTime n enc encUnary)
    (hcount : ComputableInPolyTime count enc encUnary) :
    ComputableInPolyTime
      (fun a => (supportSamplerCircuit (width a) (bits a) (n a) (count a)).code)
      enc encCode := by
  have hinput : ComputableInPolyTime (fun a => count a * width a) enc encNat :=
    unary_to_binary.comp (by fun_prop)
  have hcandidate :=
    computableInPolyTime_supportCandidateCircuit hwidth hbits hn hcount
  have hscan := computableInPolyTime_supportScanCircuit hbits (const 0) hcount
  have hindicator := computableInPolyTime_supportIndicatorCircuit hbits hn hcount
  have hcode := computableInPolyTime_compCode hinput hindicator
    (computableInPolyTime_compCode hinput hscan hcandidate)
  simpa only [compCode_code, supportSamplerCircuit] using hcode

end Cslib.Crypto.HQC
