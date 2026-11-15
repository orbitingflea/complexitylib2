/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DyadicSummation
import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.FirstEventSign

/-!
# Ordinary-import clients of dyadic summation and first-event selection

The examples check zero division, finite restriction, unary precision certificates, positive
priority, an empty range, and rejection of a later positive event after the first negative one.
No relation between these generic tests and an implicit integer is assumed.
-/

set_option linter.privateModule false

open Cslib Cslib.Complexity Turing.MultiTapeTM Finset

example : dyadicRangeSum 2 3 (fun i => i + 1) id = 2 := by decide

example (B r : ℕ) (num : ℕ → ℕ) : dyadicRangeSum B r num (fun _ => 0) = 0 := by
  simp [dyadicRangeSum]

example (r : ℕ) (num den : ℕ → ℕ) : dyadicRangeSum 0 r num den = 0 := by
  simp only [dyadicRangeSum, pow_zero, one_mul, Nat.mod_one]

example : dyadicRangeSum 3 6 (fun i => if i ∈ ({2, 5} : Finset ℕ) then i + 1 else 0) id = 5 := by
  rw [dyadicRangeSum_restrict_eq {2, 5} 3 6 (fun i => i + 1) (by decide)]
  decide

-- Precision is obtained from unary input; the endpoint is converted to binary.
example : (fun x : ℕ => dyadicRangeSum x x (fun i => i + 1) id) ∈
    CountingFunction 1 encUnary encNat := by
  apply CountingFunction.dyadicRangeSum_mem (a := 0) Decoder.unary
    (B := id) (r := id) (num := fun p : ℕ × ℕ => p.2 + 1) (den := Prod.snd)
  · exact CountingFunction.of_polyTime (by fun_prop)
  · exact CountingFunction.of_polyTime (ComputableInPolyTime.snd _ _)
  · exact ComputableInPolyTime.id'
  · exact ComputableInPolyTime.unary_to_binary

-- Both tests accept the first event: positive has priority.
example : firstEventSign (fun p : Unit × ℕ => decide (p.2 = 2))
    (fun _ => true) (fun _ => true) (fun _ => 4) () = 1 := by
  apply (firstEventSign_eq_one_iff _ _ _ _ _).mpr
  refine ⟨2, by decide, by decide, rfl, ?_⟩
  intro j hj
  have : j ≠ 2 := by omega
  simp [this]

-- A positive test at a later event cannot displace a negative test at the first event.
example : firstEventSign (fun _ : Unit × ℕ => true)
    (fun p => decide (p.2 = 1)) (fun p => decide (p.2 = 0)) (fun _ => 2) () = -1 := by
  apply (firstEventSign_eq_neg_one_iff _ _ _ _ _).mpr
  constructor
  · rintro ⟨i, _, _, hpos, hprev⟩
    have hi : i = 1 := of_decide_eq_true hpos
    subst i
    have := hprev 0 (by decide)
    contradiction
  · exact ⟨0, by decide, rfl, by decide, fun j hj => by omega⟩

example {α : Type} (event positive negative : α × ℕ → Bool) (x : α) :
    firstEventSign event positive negative (fun _ => 0) x = 0 := by
  simp [firstEventSign_eq_zero_iff]

example : firstEventSign (fun p : ℕ × ℕ => decide (p.2 = 2))
    (fun _ => true) (fun _ => false) id ∈ CountingFunction 2 encNat encIntBin := by
  apply firstEventSign_mem_CountingFunction Decoder.nat
  · exact CountingFunction.of_polyTime (by fun_prop)
  · exact CountingFunction.of_polyTime (ComputableInPolyTime.const true)
  · exact CountingFunction.of_polyTime (ComputableInPolyTime.const false)
  · exact ComputableInPolyTime.id'
