/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.BranchingProgram.Nondeterministic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi

/-! Concrete `module` clients for nondeterministic branching programs (`NBP`): contact counts,
path counts, nondeterministic and parity acceptance, and the nondeterministic program of a
deterministic one (`BranchingProgram.toNBP`). -/

public section

namespace CslibFrontierTests.NondeterministicBranchingProgram

open Cslib.BranchingPrograms

/-! ### 1. Two parallel contacts -/

/-- Two contacts `x 0` and `x 1` from the source to the target. -/
def twoContacts : NBP (Fin 2) Bool 2 :=
  .node .target [⟨0, some (0, true)⟩, ⟨0, some (1, true)⟩]

example : twoContacts.size = 2 := by
  decide

example : twoContacts.pathCount ![true, true] = 2 := by
  decide

/-- With nondeterministic acceptance the two contacts compute the disjunction. -/
example : ∀ x : Fin 2 → Bool, twoContacts.Accepts x ↔ (x 0 || x 1) = true := by
  decide

/-- With parity acceptance the same program computes the exclusive disjunction. -/
example : ∀ x : Fin 2 → Bool, twoContacts.AcceptsParity x ↔ (x 0 ^^ x 1) = true := by
  decide

/-! ### 2. Markov's monotone program for the majority of three bits -/

/-- A monotone program for "at least two of three bits" with four contacts, the number
`k * (n - k + 1)` of [Jukna, Corollary 1.9][Jukna2012] for `n = 3` and `k = 2`. Node `4`, the
source, has seen no `1` and reads `x 0` next; node `3` has seen no `1` and reads `x 1` next;
node `2` has seen one `1` and reads `x 1` next; node `1` has seen one `1` and reads `x 2` next;
node `0` is the target. Rectifiers skip a bit. -/
def majorityThree : NBP (Fin 3) Bool 5 :=
  NBP.target
    |>.node [⟨0, some (2, true)⟩]
    |>.node [⟨1, none⟩, ⟨0, some (1, true)⟩]
    |>.node [⟨1, some (1, true)⟩]
    |>.node [⟨3, none⟩, ⟨2, some (0, true)⟩]

example : majorityThree.size = 4 := by
  decide

example : ∀ x : Fin 3 → Bool,
    majorityThree.Accepts x ↔ ((x 0 && x 1) || (x 0 && x 2) || (x 1 && x 2)) = true := by
  decide

/-- Three ones switch on all three paths. -/
example : majorityThree.pathCount ![true, true, true] = 3 := by
  decide

/-! ### 3. Deterministic programs -/

/-- A deterministic program computing `x 0 && x 1` with two query nodes and two sinks. -/
def andProgram : BranchingProgram (Fin 2) Bool where
  nodes := BranchingProgram.Nodes.empty
    |>.node (.sink false)
    |>.node (.sink true)
    |>.node (.branch 1 fun b => if b then 1 else 0)
    |>.node (.branch 0 fun b => if b then 2 else 0)
  start := 3

/-- The nondeterministic program of `andProgram` switches on one path exactly on the inputs
`andProgram` accepts. -/
example (x : Fin 2 → Bool) :
    andProgram.toNBP.pathCount x = if andProgram.eval x then 1 else 0 :=
  andProgram.pathCount_toNBP x

/-- It has at most two contacts for each of the four nodes. -/
example : andProgram.toNBP.size ≤ Fintype.card Bool * 4 :=
  andProgram.size_toNBP_le

end CslibFrontierTests.NondeterministicBranchingProgram
