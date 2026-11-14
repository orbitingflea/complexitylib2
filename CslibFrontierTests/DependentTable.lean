/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi

/-! Dependent and canonical-order finite tables with unbounded words, an empty alphabet, and no
indices. -/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.DependentTable

open Turing.MultiTapeTM ComputableInPolyTime

private def Entry : Bool → Type
  | false => List Empty
  | true => List Bool

private def encEmpty : Empty ↪ List Bool := ⟨Empty.elim, fun value => value.elim⟩

private noncomputable def encoding : ∀ i, Entry i ↪ List Bool
  | false => encList encEmpty
  | true => encBits

-- This family is inhabited even though one stack's alphabet is empty. Its other stack may grow.
private def table (bits : List Bool) : ∀ i, Entry i
  | false => []
  | true => bits

example : ComputableInPolyTime table encBits (encDPi encoding) := by
  apply dpi
  intro i
  cases i
  · exact const []
  · exact id'

example : ComputableInPolyTime (fun values : ∀ i, Entry i => values true)
    (encDPi encoding) encBits := dpi_apply encoding true

-- Reading the unbounded word, reversing it, and replacing it preserves the empty-alphabet entry.
example : ComputableInPolyTime
    (fun values : ∀ i, Entry i => Function.update values true (values true).reverse)
    (encDPi encoding) (encDPi encoding) :=
  dpi_update id' (bitsReverse.comp (dpi_apply encoding true))

example (bits : List Bool) : Function.update (table bits) true bits.reverse false = [] := by
  exact Function.update_of_ne (β := Entry) (a := false) (a' := true)
    (by decide) bits.reverse (table bits)

-- The finite family with no indices still has one value and requires no entry inhabitant.
example : ComputableInPolyTime
    (fun _ : List Bool => (Empty.elim : Empty → Empty)) encBits
    (encDPi (fun i : Empty => i.elim)) := by
  apply dpi
  intro i
  exact i.elim

example : encDPi (fun i : Empty => i.elim) (Empty.elim : Empty → Empty) = [] := by
  apply List.length_eq_zero_iff.mp
  rw [length_encDPi]
  simp

-- Computable canonical-order `Fin` unary codes via `encFinEnum (Fin count)` equal `encUnary i.val`
-- and have length strictly less than `count`.
example (i : Fin 5) : encFinEnum (Fin 5) i = encUnary i.val :=
  encFinEnum_fin_apply i

example (i : Fin 5) : (encFinEnum (Fin 5) i).length < Nat.card (Fin 5) :=
  length_encFinEnum_lt i

-- Construct and index a canonical-order `Fin 3 → List Bool` table of unbounded words without
-- importing BCS.
private def wordFamily (bits : List Bool) : Fin 3 → List Bool
  | ⟨0, _⟩ => bits
  | ⟨1, _⟩ => bits.reverse
  | ⟨_ + 2, _⟩ => bits ++ bits

private theorem computableInPolyTime_wordFamily :
    ComputableInPolyTime wordFamily encBits (encFinFn 3 encBits) := by
  apply finFn
  intro i
  fin_cases i
  · exact id'
  · exact bitsReverse
  · exact bitsAppend id' id'

example :
    ComputableInPolyTime
      (fun p : List Bool × Fin 3 => wordFamily p.1 p.2)
      (encPair encBits (encFinEnum (Fin 3))) encBits :=
  finFn_apply'
    (computableInPolyTime_wordFamily.comp (fst encBits (encFinEnum (Fin 3))))
    (snd encBits (encFinEnum (Fin 3)))

example :
    wordFamily [true, false] ⟨1, by decide⟩ = [false, true] ∧
      wordFamily [true, false] ⟨2, by decide⟩ = [true, false, true, false] :=
  ⟨rfl, rfl⟩

end CslibFrontierTests.DependentTable
