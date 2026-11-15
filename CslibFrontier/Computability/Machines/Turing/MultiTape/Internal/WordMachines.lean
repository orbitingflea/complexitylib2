/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.KernelTransducer

/-! # Zero-workspace word machines

Shared finite-state programs and their word semantics, independent of resource facades.
-/

public section
namespace Turing.MultiTapeTM.Internal.WordMachines

/-- Emit one mapped bit per input symbol. -/
@[expose] def mapT (f : Bool → Bool) : Transducer Bool Unit :=
  ⟨(), fun _ b => ((), [f b]), fun _ => [], by simp, by simp⟩

/-- The map machine emits exactly the mapped word. -/
theorem mapT_run (f : Bool → Bool) (l : List Bool) :
    (mapT f).run () l = l.map f := by
  induction l with
  | nil => rfl
  | cons b l ih => simpa [mapT, Transducer.run] using congrArg (List.cons (f b)) ih

/-- Buffer one bit so the final bit is omitted. -/
@[expose] def dropLastT : Transducer Bool (Option Bool) where
  q₀ := none
  step
    | none, b => (some b, [])
    | some prev, b => (some b, [prev])
  final _ := []
  length_step_le q b := by cases q <;> simp
  length_final_le _ := by simp

/-- Starting with a buffered bit emits the prefix of the buffered word. -/
theorem dropLastT_run_some (prev : Bool) (l : List Bool) :
    dropLastT.run (some prev) l = (prev :: l).dropLast := by
  induction l generalizing prev with
  | nil => rfl
  | cons b l ih =>
    simpa only [dropLastT, Transducer.run_cons, List.singleton_append,
      List.dropLast_cons_cons] using congrArg (List.cons prev) (ih b)

/-- The initial empty buffer drops precisely the last input bit. -/
theorem dropLastT_run (l : List Bool) : dropLastT.run none l = l.dropLast := by
  cases l with
  | nil => rfl
  | cons b l =>
    simpa only [dropLastT, Transducer.run_cons, List.nil_append] using dropLastT_run_some b l

/-- The finite-state transducer that remembers the last bit read and ends with `final` of it. -/
@[expose] def lastBitT (final : Option Bool → List Bool) (hfinal : ∀ q, (final q).length ≤ 2) :
    Transducer Bool (Option Bool) where
  q₀ := none
  step _ b := (some b, [])
  final := final
  length_step_le _ _ := by simp
  length_final_le := hfinal

theorem run_lastBitT (final : Option Bool → List Bool) (hfinal : ∀ q, (final q).length ≤ 2)
    (l : List Bool) :
    (lastBitT final hfinal).run (lastBitT final hfinal).q₀ l = final l.getLast? := by
  suffices ∀ q, (lastBitT final hfinal).run q l = final (l.getLast?.or q) from
    (this none).trans (by rw [Option.or_none])
  induction l with
  | nil => intro q; rfl
  | cons b l ih =>
    intro q
    rw [Transducer.run_cons, ih, List.getLast?_cons]
    cases l.getLast? <;> rfl

end Turing.MultiTapeTM.Internal.WordMachines
