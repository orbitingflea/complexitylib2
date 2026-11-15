/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Equality

/-!
# Named native unary comparison

This module retains a direct zip transducer for strict comparison of unary naturals. The machine
copies the first word once, scans both unary words in lockstep, and distinguishes which word ends
first. Both the one-bit Boolean result and the empty/nonempty branch-test result retain actual
machines and the construction formulas from `NativeCompiler.ofZipTransducer`.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryLtBool`: strict unary comparison with one-bit
  output.
* `Turing.MultiTapeTM.Internal.NativeCompiler.unaryLtTest`: the same comparison in branch-test
  encoding.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Record whether the right unary word extends beyond the left unary word. -/
def unaryLtT : ZipTransducer Bool where
  q₀ := false
  step _ symbols := (symbols.1.isNone && symbols.2.isSome, [])
  final less := [less]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem unaryLtT_run_nil_right (n : ℕ) :
    unaryLtT.run true [] (List.replicate n true) = [true] := by
  induction n with
  | zero => simp only [List.replicate_zero, ZipTransducer.run_nil_nil, unaryLtT]
  | succ n ih =>
      simpa only [List.replicate_succ, ZipTransducer.run_nil_cons, unaryLtT,
        Option.isNone_none, Option.isSome_some, Bool.true_and, List.nil_append] using ih

private theorem unaryLtT_run_left_nil (n : ℕ) :
    unaryLtT.run false (List.replicate n true) [] = [false] := by
  induction n with
  | zero => simp only [List.replicate_zero, ZipTransducer.run_nil_nil, unaryLtT]
  | succ n ih =>
      simpa only [List.replicate_succ, ZipTransducer.run_cons_nil, unaryLtT,
        Option.isNone_some, Bool.false_and, List.nil_append] using ih

/-- The comparison transducer returns the strict order of the two unary lengths. -/
theorem unaryLtT_run (left right : ℕ) :
    unaryLtT.run unaryLtT.q₀ (encUnary left) (encUnary right) =
      encBool (decide (left < right)) := by
  induction left generalizing right with
  | zero =>
      cases right with
      | zero =>
          simp only [encUnary_apply, List.replicate_zero, ZipTransducer.run_nil_nil,
            unaryLtT, Nat.lt_irrefl, decide_false, encBool_apply]
      | succ right =>
          simp only [encUnary_apply, List.replicate_zero, List.replicate_succ,
            ZipTransducer.run_nil_cons, unaryLtT, Option.isNone_none,
            Option.isSome_some, Bool.true_and, List.nil_append, Nat.zero_lt_succ,
            decide_true, encBool_apply]
          exact unaryLtT_run_nil_right right
  | succ left ih =>
      cases right with
      | zero =>
          simp only [encUnary_apply, List.replicate_succ, List.replicate_zero,
            ZipTransducer.run_cons_nil, unaryLtT, Option.isNone_some,
            Bool.false_and, List.nil_append, Nat.not_lt_zero, decide_false, encBool_apply]
          exact unaryLtT_run_left_nil left
      | succ right =>
          simp only [encUnary_apply, List.replicate_succ, ZipTransducer.run_cons_cons,
            unaryLtT, Option.isNone_some, Bool.false_and, List.nil_append,
            Nat.succ_lt_succ_iff, encBool_apply]
          exact ih right

/-- Strict comparison of unary naturals, emitting the standard one-bit Boolean encoding. -/
@[expose] noncomputable def unaryLtBool :
    NativeCompiler (fun input : ℕ × ℕ => decide (input.1 < input.2))
      (encPair encUnary encUnary) encBool :=
  ofZipTransducer encUnary encUnary encBool unaryLtT Universal.eBit fun input =>
    unaryLtT_run input.1 input.2

/-- Strict comparison of unary naturals in the empty/nonempty branch-test encoding. -/
@[expose] noncomputable def unaryLtTest :
    NativeCompiler (fun input : ℕ × ℕ => decide (input.1 < input.2))
      (encPair encUnary encUnary) encTest :=
  boolToTest.comp unaryLtBool

end Turing.MultiTapeTM.Internal.NativeCompiler
