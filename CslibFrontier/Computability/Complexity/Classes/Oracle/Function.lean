/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic

/-!
# Composition of deterministic oracle functions

These rules retain one fixed language oracle and one uniform strict polynomial-time program.
Adaptive composition charges the intermediate encoding, subsequent requests, and final output.
The strict certificate already bounds output length polynomially.

## Main results

* `Cslib.Complexity.ComputableInPolyTimeWithOracle.comp`: adaptive composition.
* `Cslib.Complexity.ComputableInPolyTimeWithOracle.comp_with`: composition retaining the input.
-/

public section

namespace Cslib.Complexity.ComputableInPolyTimeWithOracle

open Probability Turing.MultiTapeTM

variable {α β γ : Type} {A : Set (List Bool)} {input : α ↪ List Bool}
  {middle : β ↪ List Bool} {output : γ ↪ List Bool}

/-- Sequential composition against one fixed oracle. Later requests may depend on the first
result; both programs have a uniform clock even against arbitrary stateful replies. -/
theorem comp {f : β → γ} {g : α → β}
    (hf : ComputableInPolyTimeWithOracle A f middle output)
    (hg : ComputableInPolyTimeWithOracle A g input middle) :
    ComputableInPolyTimeWithOracle A (fun a => f (g a)) input output := by
  obtain ⟨first, hfirst, hfirst_eq⟩ := hg
  obtain ⟨second, hsecond, hsecond_eq⟩ := hf
  refine ⟨fun a => first a >>= second, ?_, fun a => ?_⟩
  · simpa only [OracleComp.interpret_bind] using hfirst.bind hsecond
  · simp only [OracleComp.interpret_bind, hfirst_eq, hsecond_eq]
    rfl

/-- Retain the input for an adaptive second computation, charging its encoded copy. -/
theorem comp_with {f : α × β → γ} {g : α → β}
    (hf : ComputableInPolyTimeWithOracle A f (encPair input middle) output)
    (hg : ComputableInPolyTimeWithOracle A g input middle) :
    ComputableInPolyTimeWithOracle A (fun a => f (a, g a)) input output :=
  hf.comp ((ComputableInPolyTime.id'.computableInPolyTimeWithOracle A).prod hg)

end Cslib.Complexity.ComputableInPolyTimeWithOracle
