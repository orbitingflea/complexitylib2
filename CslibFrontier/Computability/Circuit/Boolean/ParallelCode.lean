/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CodeComposition
public import CslibFrontier.Computability.Circuit.Replication
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Native code for circuit families on disjoint inputs

`parallelFamilyCode n m codes` runs an arbitrary list of `n`-input, `m`-output circuit codes on
consecutive disjoint input blocks and concatenates their output blocks.  The fold mirrors
`Circuit.parallelFamily`: it retains each member's internal sharing and never compiles a truth
table.

## Main definitions

* `Cslib.Circuits.Boolean.parallelFamilyCode`: raw code for a list of disjoint-input circuits.

## Main results

* `Cslib.Circuits.Boolean.parallelFamilyCode_code`: exact agreement with
  `Circuit.parallelFamily` for every finite family.
* `Cslib.Circuits.Boolean.computableInPolyTime_parallelFamilyCodeStep`: polynomial-time
  generation of the fold step used by the compiler.

These code-composition results are original infrastructure.
-/

public section

namespace Cslib.Circuits.Boolean

open Turing.MultiTapeTM ComputableInPolyTime

local notation "Code" => List (Op × List ℕ) × List ℕ

/-- Run two raw circuit codes on consecutive disjoint input blocks.  This binary constructor is
kept private as the implementation step of the list-level family compiler. -/
private def parallelCode (leftInputs rightInputs : ℕ) (left right : Code) : Code :=
  appendCode (leftInputs + rightInputs)
    (compCode (leftInputs + rightInputs) left ([], List.range leftInputs))
    (compCode (leftInputs + rightInputs) right
      ([], (List.range rightInputs).map (leftInputs + ·)))

private theorem parallelCode_code {n m p q : ℕ}
    (left : Circuit signature n m) (right : Circuit signature p q) :
    parallelCode n p left.code right.code = (left.parallel right).code := by
  rw [parallelCode, Circuit.parallel]
  rw [show ([], List.range n) = (Circuit.wiring signature (Fin.castAdd p)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.castAdd p) (g := id) (fun _ => rfl)]
  rw [show ([], (List.range p).map (n + ·)) =
      (Circuit.wiring signature (Fin.natAdd n)).code by
    symm
    simpa using Circuit.code_wiring_eq_map
      (σ := signature) (f := Fin.natAdd n) (g := (n + ·)) (fun _ => rfl)]
  rw [compCode_code, compCode_code, appendCode_code]

/-- Extend a disjoint-input parallel-family prefix by one raw circuit code. The parameter pair is
the common input and output width. -/
@[expose] def parallelFamilyCodeStep (par : ℕ × ℕ) (state : ℕ × Code) (code : Code) :
    ℕ × Code :=
  let k := state.1
  let inputCount := (k + 1) * par.1
  let outputCount := (k + 1) * par.2
  let combined := appendCode (k * par.1 + par.1)
    (compCode (k * par.1 + par.1) state.2 ([], List.range (k * par.1)))
    (compCode (k * par.1 + par.1) code
      ([], (List.range par.1).map (k * par.1 + ·)))
  (k + 1,
    compCode inputCount ([], List.range outputCount)
      (compCode inputCount combined ([], List.range inputCount)))

/-- The compiler's single extension step is polynomial-time computable under the fold encoding. -/
@[fun_prop] theorem computableInPolyTime_parallelFamilyCodeStep :
    ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        parallelFamilyCodeStep p.1.1 p.1.2 p.2)
      (encFoldStep (encPair encUnary encUnary) (encPair encUnary encCode) encCode)
      (encPair encUnary encCode) := by
  let stepEnc := encFoldStep (encPair encUnary encUnary)
    (encPair encUnary encCode) encCode
  have hn : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.1.1)
      stepEnc encUnary := by fun_prop
  have hm : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.1.2)
      stepEnc encUnary := by fun_prop
  have hk : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.2.1)
      stepEnc encUnary := by fun_prop
  have hstate : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.2.2)
      stepEnc encCode := by fun_prop
  have hcode : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.2)
      stepEnc encCode := by fun_prop
  have hk1 : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.2.1 + 1)
      stepEnc encUnary := by fun_prop
  have hprefixInputs : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) => p.1.2.1 * p.1.1.1)
      stepEnc encUnary := by fun_prop
  have hblockInputs : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        p.1.2.1 * p.1.1.1 + p.1.1.1) stepEnc encUnary := by fun_prop
  have hinputCount : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        (p.1.2.1 + 1) * p.1.1.1) stepEnc encUnary := by fun_prop
  have houtputCount : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        (p.1.2.1 + 1) * p.1.1.2) stepEnc encUnary := by fun_prop
  have hprefixRange : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        ([], List.range (p.1.2.1 * p.1.1.1))) stepEnc encCode :=
    (const (encOut := encList encGate) []).prod (by
      simpa only [Function.comp_def, List.map_id_fun', id_eq] using
        unary_to_binary.map.comp (range.comp hprefixInputs))
  have hinputRange : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        ([], List.range ((p.1.2.1 + 1) * p.1.1.1))) stepEnc encCode :=
    (const (encOut := encList encGate) []).prod (by
      simpa only [Function.comp_def, List.map_id_fun', id_eq] using
        unary_to_binary.map.comp (range.comp hinputCount))
  have houtputRange : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        ([], List.range ((p.1.2.1 + 1) * p.1.1.2))) stepEnc encCode :=
    (const (encOut := encList encGate) []).prod (by
      simpa only [Function.comp_def, List.map_id_fun', id_eq] using
        unary_to_binary.map.comp (range.comp houtputCount))
  have hshiftedRange : ComputableInPolyTime
      (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
        ([], (List.range p.1.1.1).map (p.1.2.1 * p.1.1.1 + ·))) stepEnc encCode := by
    have hwire : ComputableInPolyTime
        (fun q : ((((ℕ × ℕ) × (ℕ × Code)) × Code) × ℕ) =>
          q.1.1.2.1 * q.1.1.1.1 + q.2) (encPair stepEnc encUnary) encNat :=
      unary_to_binary.comp (by fun_prop)
    exact (const (encOut := encList encGate) []).prod
      (mapWithInput (range.comp hn) hwire)
  have hleft := computableInPolyTime_compCode (unary_to_binary.comp hblockInputs)
    hstate hprefixRange
  have hright := computableInPolyTime_compCode (unary_to_binary.comp hblockInputs)
    hcode hshiftedRange
  have hcombined := computableInPolyTime_appendCode (unary_to_binary.comp hblockInputs)
    hleft hright
  have hinner := computableInPolyTime_compCode (unary_to_binary.comp hinputCount)
    hcombined hinputRange
  have hfinal := computableInPolyTime_compCode (unary_to_binary.comp hinputCount)
    houtputRange hinner
  change ComputableInPolyTime
    (fun p : (((ℕ × ℕ) × (ℕ × Code)) × Code) =>
      parallelFamilyCodeStep p.1.1 p.1.2 p.2) stepEnc (encPair encUnary encCode)
  exact hk1.prod hfinal

/-- Run a list of raw `n`-input, `m`-output circuit codes on consecutive disjoint input blocks,
preserving the list order in the output blocks. -/
@[expose] def parallelFamilyCode (n m : ℕ) (codes : List Code) : Code :=
  (codes.foldl (parallelFamilyCodeStep (n, m)) (0, ([], []))).2

/-- Folding the shared extension step over a typed family records its length and produces exactly
the typed parallel-family code. -/
theorem foldl_parallelFamilyCodeStep_code {k n m : ℕ}
    (cs : Fin k → Circuit signature n m) :
    (List.ofFn fun j => (cs j).code).foldl
      (parallelFamilyCodeStep (n, m)) (0, ([], [])) =
      (k, (Circuit.parallelFamily cs).code) := by
  induction k with
  | zero => simp [Circuit.parallelFamily, Circuit.code_wiring]
  | succ k ih =>
    rw [List.ofFn_succ_last, List.foldl_append, ih (fun j => cs j.castSucc)]
    simp only [List.foldl_cons, List.foldl_nil, parallelFamilyCodeStep]
    have hout : (Circuit.wiring signature (Fin.cast (Nat.succ_mul k m))).code =
        ([], List.range ((k + 1) * m)) := by
      simpa [Nat.succ_eq_add_one, Nat.succ_mul] using Circuit.code_wiring_eq_map
        (σ := signature) (f := Fin.cast (Nat.succ_mul k m)) (g := id) fun _ => rfl
    have hin : (Circuit.wiring signature (Fin.cast (Nat.succ_mul k n).symm)).code =
        ([], List.range ((k + 1) * n)) := by
      simpa [Nat.succ_eq_add_one, Nat.succ_mul] using Circuit.code_wiring_eq_map
        (σ := signature) (f := Fin.cast (Nat.succ_mul k n).symm) (g := id) fun _ => rfl
    have hparallel :
        appendCode (k * n + n)
          (compCode (k * n + n) (Circuit.parallelFamily fun j => cs j.castSucc).code
            ([], List.range (k * n)))
          (compCode (k * n + n) (cs (Fin.last k)).code
            ([], (List.range n).map (k * n + ·))) =
          ((Circuit.parallelFamily fun j => cs j.castSucc).parallel
            (cs (Fin.last k))).code := by
      simpa only [parallelCode] using parallelCode_code
        (Circuit.parallelFamily fun j => cs j.castSucc) (cs (Fin.last k))
    rw [← hout, ← hin, hparallel, compCode_code, compCode_code]
    rfl

/-- Compiling the codes of a typed finite family gives exactly the code of its disjoint-input
parallel composition, including the empty family. -/
theorem parallelFamilyCode_code {k n m : ℕ} (cs : Fin k → Circuit signature n m) :
    parallelFamilyCode n m (List.ofFn fun j => (cs j).code) =
      (Circuit.parallelFamily cs).code := by
  unfold parallelFamilyCode
  rw [foldl_parallelFamilyCodeStep_code]

end Cslib.Circuits.Boolean
