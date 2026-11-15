/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import Mathlib.Tactic.FunProp
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Transducer
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.Reverse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.WordMachines

/-! # Exact resources for word transducers

These numerical bounds exclude output from workspace. In particular, a map can emit an
arbitrarily long word with zero workspace. Last-bit outputs have independent constant size.
-/

public section
namespace Turing.MultiTapeTM
open Internal.WordMachines

attribute [fun_prop] ComputableInTimeAndSpace

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.map_bits (f : Bool → Bool) :
    ComputableInTimeAndSpace (List.map f) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  (mapT f).computableInTimeAndSpace fun l => (mapT_run f l).symm

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.reverse_bits :
    ComputableInTimeAndSpace List.reverse encBits encBits
      (fun l => 2 * l.length + 2) (fun _ => 0) :=
  computableInTimeAndSpace_reverse fun _ => rfl

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.length_bits :
    ComputableInTimeAndSpace List.length encBits encUnary
      (fun l => 4 * l.length + 8) (fun _ => 0) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := map_bits (fun _ => true)
  refine ⟨k, State, hfin, tm, fun l => ?_⟩
  have hmap : List.map (fun _ => true) l = encUnary l.length := by
    simp [encUnary_apply, List.map_const']
  exact hmap ▸ htm l

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.dropLast_bits :
    ComputableInTimeAndSpace List.dropLast encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  dropLastT.computableInTimeAndSpace fun l => (dropLastT_run l).symm

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.getLast?_toList_bits :
    ComputableInTimeAndSpace (fun l : List Bool => l.getLast?.toList) encBits encBits
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  (lastBitT Option.toList fun q => by cases q <;> simp).computableInTimeAndSpace fun l =>
    (run_lastBitT Option.toList _ l).symm

/-- Exact time and zero workspace for this word operation. -/
@[fun_prop]
theorem ComputableInTimeAndSpace.getLast?_bits :
    ComputableInTimeAndSpace (List.getLast? (α := Bool)) encBits (encOption encBool)
      (fun l => 4 * l.length + 8) (fun _ => 0) :=
  (lastBitT (encOption encBool) fun q => by cases q <;> simp).computableInTimeAndSpace
    fun l => (run_lastBitT (encOption encBool) _ l).symm

end Turing.MultiTapeTM
