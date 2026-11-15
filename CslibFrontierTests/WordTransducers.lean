/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: local-only (tests of exact word resource facades)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.WordTransducers

/-! # Plain exact word-resource regression

The facade alone supplies automation and numerical zero-workspace certificates.
The output-charge counterexample distinguishes workspace from returned storage.
-/

open Turing.MultiTapeTM

example : ComputableInTimeAndSpace (List.map Bool.not) encBits encBits
    (fun l => 4 * l.length + 8) (fun _ => 0) := by fun_prop

example : ComputableInTimeAndSpace List.reverse encBits encBits
    (fun l => 2 * l.length + 2) (fun _ => 0) := by fun_prop

example : ComputableInTimeAndSpace (List.getLast? (α := Bool)) encBits (encOption encBool)
    (fun l => 4 * l.length + 8) (fun _ => 0) := by fun_prop

example : ComputableInTimeAndSpace List.length encBits encUnary
    (fun l => 4 * l.length + 8) (fun _ => 0) := by fun_prop

example : ComputableInTimeAndSpace (List.dropLast (α := Bool)) encBits encBits
    (fun l => 4 * l.length + 8) (fun _ => 0) := by fun_prop

example : ComputableInTimeAndSpace (fun l : List Bool => l.getLast?.toList) encBits encBits
    (fun l => 4 * l.length + 8) (fun _ => 0) := by fun_prop

-- Mixed streaming leaves must not become prerequisites of this plain entry point.
example : True := by
  fail_if_success have := ComputableTidilyInTimeAndSpace.map_bits
  trivial

-- Zero workspace cannot supply the output-size premise for charged constant space.
example : ¬ ∃ c : ℕ, ∀ l : List Bool, (l.map Bool.not).length ≤ c * (0 + 1) := by
  rintro ⟨c, hc⟩
  have h := hc (List.replicate (c + 1) false)
  simp only [List.length_map, List.length_replicate, Nat.zero_add, Nat.mul_one] at h
  omega
