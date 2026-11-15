/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.Plain
public meta import Lean.Elab.Command

/-!
# Degree certificate views for encoding generators

The structure and inductive generators share proof terms for linear time/space, input-length
workspace and polynomial time. Their declaration binders, visibility, registration and composition
contracts remain with each generator. No transition rule is registered globally.
-/

public meta section

namespace Turing.MultiTapeTM.Internal

open Lean

/-- Proof terms for the linear, input-length workspace and polynomial views of a degree
certificate with cost degree one. Its output degree is unrestricted. The certificate term may
include explicit parameters; generated declarations retain their caller's binders. -/
def linearDegreeViews (degree : Term) : MacroM (Term × Term × Term) := do
  let linear ← `(ComputableInDegree.inO_one $degree)
  let space ← `(ComputableInSpace.of_inO $linear)
  let polynomial ← `(ComputableInDegree.computableInPolyTime $degree)
  return (linear, space, polynomial)

end Turing.MultiTapeTM.Internal
