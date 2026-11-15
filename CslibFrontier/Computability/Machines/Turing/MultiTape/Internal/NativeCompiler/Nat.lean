/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.NativeCompiler.Codec

/-!
# Named native binary-natural primitives

This module retains the existing streaming successor, predecessor and zero-test transducers as
`NativeCompiler`s. The wrappers name the concrete machines and their constructive state encodings;
they do not extract a witness from the existential complexity certificates.

## Main definitions

* `Turing.MultiTapeTM.Internal.NativeCompiler.natSucc`: retained binary successor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natPred`: retained saturating binary predecessor.
* `Turing.MultiTapeTM.Internal.NativeCompiler.natIsZeroBool`, `.natIsZeroTest`: retained binary
  zero tests in Boolean and branch-test encodings.
-/

public section

namespace Turing.MultiTapeTM.Internal.NativeCompiler

/-- Binary successor through the public carry transducer. -/
@[expose] noncomputable def natSucc :
    NativeCompiler (fun n : ℕ => n + 1) encNat encNat :=
  ofTransducer NatSucc.succTransducer Universal.eBit fun n => by
    simpa only [encNat_apply] using NatSucc.run_succTransducer_q₀ n

/-- Saturating binary predecessor through the public borrow transducer. -/
@[expose] noncomputable def natPred :
    NativeCompiler (fun n : ℕ => n - 1) encNat encNat :=
  ofTransducer NatPred.predTransducer (optionStateEncoding Universal.eBit) fun n => by
    simpa only [encNat_apply] using NatPred.run_predTransducer_q₀ n

/-- Binary zero test with one-bit Boolean output. -/
@[expose] noncomputable def natIsZeroBool :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encBool :=
  ofTransducer NatPred.isZeroTransducer Universal.eBit fun n => by
    simpa only [encNat_apply, encBool_apply] using NatPred.run_isZeroTransducer_q₀ n

/-- Binary zero test in the empty/nonempty branch encoding, including the retained conversion. -/
@[expose] noncomputable def natIsZeroTest :
    NativeCompiler (fun n : ℕ => decide (n = 0)) encNat encTest :=
  boolToTest.comp natIsZeroBool

/-- The retained successor compiler uses the concrete carry transducer. -/
theorem machine_natSucc : natSucc.machine =
    NatSucc.succTransducer.toTM.seq (rewindInput Bool) :=
  rfl

/-- The retained predecessor compiler uses the concrete borrow transducer. -/
theorem machine_natPred : natPred.machine =
    NatPred.predTransducer.toTM.seq (rewindInput Bool) :=
  rfl

end Turing.MultiTapeTM.Internal.NativeCompiler
