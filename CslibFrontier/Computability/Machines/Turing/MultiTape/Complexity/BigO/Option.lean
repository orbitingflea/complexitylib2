/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OOptionPrimitives

/-!
# Parameterized option elimination with retained input

The arbitrary-resource rule `Turing.MultiTapeTM.ComputableInO.optionElimWithInput` is provided
by the native option primitives, also used by polynomial-time option elimination. This entry
point retains the quantitative `fun_prop` calculus for existing clients. The selected handler
receives the original input and its payload; time and charged space remain independent.
-/

public section

attribute [fun_prop] Turing.MultiTapeTM.ComputableInO.optionElimWithInput
