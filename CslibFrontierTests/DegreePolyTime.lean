/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (degree-to-polynomial transition experiment)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Option

/-!
# Degree discovery through a local polynomial-time transition

Test-only irreducible operations prevent discovery by unfolding to existing polynomial wrappers.
Only degree rules are registered for them. There is no degree hypothesis in any client goal.
The degree parameters are arguments of the operations, so rule matching must recover independent
cost/output indices rather than obtain them from a supplied certificate. These deliberately weak
bounds are an automation experiment, not new complexity results or production migrations.

Compare each named `explicit*`/`transition*` pair with disposable hosted profiling. Normal tests
remain silent under `--iofail`. Comparative timings are pending; successful elaboration alone
establishes neither the measured search route nor an improvement. Registration is local and makes
no recommendation about the global rule set.
-/

-- Disposable test operations and timing clients are intentionally private.
set_option linter.privateModule false

namespace CslibFrontierTests.DegreePolyTime

open Turing.MultiTapeTM

-- Distinct names isolate degree-only discovery from the primitive's polynomial wrappers.
@[irreducible] private def pack (_d _e : ℕ) (bits : List Bool) : Option (List Bool) := some bits
@[irreducible] private def flag (_d : ℕ) (value : Option (List Bool)) : Bool := value.isSome

private theorem pack_deg (d e : ℕ) :
    ComputableInDegree (pack d e) encBits (encOption encBits) (d + 1) (e + 1) := by
  unfold pack
  exact ComputableInDegree.optionSome.mono (by omega) (by omega)

private theorem flag_deg (d : ℕ) :
    ComputableInDegree (flag d) (encOption encBits) encBool (d + 1) 0 := by
  unfold flag
  exact (ComputableInDegree.isSome encBits).mono (by omega) (by omega)

attribute [local fun_prop] pack_deg flag_deg

-- First check discovery at degree level, without any polynomial transition.
example (d e : ℕ) :
    ComputableInDegree (pack d e) encBits (encOption encBits) (d + 1) (e + 1) := by
  fun_prop

example (d : ℕ) :
    ComputableInDegree (flag d) (encOption encBits) encBool (d + 1) 0 := by
  fun_prop

-- The negative control must fail before local transition registration. If another search path
-- makes this succeed, investigate that path instead of interpreting it as transition evidence.
example (d e : ℕ) : ComputableInPolyTime (pack d e) encBits (encOption encBits) := by
  fail_if_success fun_prop
  exact (pack_deg d e).computableInPolyTime

private theorem explicitPack (d e : ℕ) :
    ComputableInPolyTime (pack d e) encBits (encOption encBits) :=
  (pack_deg d e).computableInPolyTime

private theorem explicitFlag (d : ℕ) :
    ComputableInPolyTime (flag d) (encOption encBits) encBool :=
  (flag_deg d).computableInPolyTime

private theorem explicitComposition (d e k : ℕ) :
    ComputableInPolyTime (fun bits => flag k (pack d e bits)) encBits encBool :=
  ((flag_deg k).comp (pack_deg d e)).computableInPolyTime

section LocalTransition

attribute [local fun_prop] ComputableInDegree.computableInPolyTime

private theorem transitionPack (d e : ℕ) :
    ComputableInPolyTime (pack d e) encBits (encOption encBits) := by
  fun_prop

private theorem transitionFlag (d : ℕ) :
    ComputableInPolyTime (flag d) (encOption encBits) encBool := by
  fun_prop

private theorem transitionComposition (d e k : ℕ) :
    ComputableInPolyTime (fun bits => flag k (pack d e bits)) encBits encBool := by
  fun_prop

-- Force search at degree level too: polynomial composition might otherwise lift each leaf
-- separately. Preserve the product of output degrees, including the Boolean output's zero.
example (d e k : ℕ) :
    ComputableInDegree (fun bits => flag k (pack d e bits)) encBits encBool
      (max (d + 1) ((e + 1) * (k + 1))) ((e + 1) * 0) := by
  fun_prop

end LocalTransition

-- Local transition registration must not escape its section.
example : ComputableInPolyTime (pack 2 0) encBits (encOption encBits) := by
  fail_if_success fun_prop
  exact (pack_deg 2 0).computableInPolyTime

end CslibFrontierTests.DegreePolyTime
