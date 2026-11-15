/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module

import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.DyadicFirstFlag
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Ordinary-import clients of the first dyadic flag classifier

The examples check both strict sides, later flagged values being ignored, zero margin denominator,
zero precision, an exact-half flag, an empty range and the actual counting-function certificate.
-/

set_option linter.privateModule false

open Cslib Cslib.Complexity Turing.MultiTapeTM

-- Zero is unflagged; the first flag is 3/8. The later 6/8 flag must be ignored.
example : dyadicFirstFlagSign 4 3 3 (fun k => if k = 0 then 0 else if k = 1 then 3 else 6) = 1 := by
  apply (dyadicFirstFlagSign_eq_one_iff (by decide) _).mpr
  refine ⟨1, by decide, ?_, by norm_num⟩
  constructor
  · norm_num [CircleFlag]
  · intro j hj
    have : j = 0 := by omega
    subst j
    norm_num [CircleFlag]

-- The first flag is 5/8; the later 3/8 flag cannot change its classification.
example : dyadicFirstFlagSign 4 3 2 (fun k => if k = 0 then 5 else 3) = -1 := by
  apply (dyadicFirstFlagSign_eq_neg_one_iff (by decide) _).mpr
  refine ⟨0, by decide, ?_, by norm_num⟩
  exact ⟨by norm_num [CircleFlag], fun j hj => by omega⟩

example (B r : ℕ) (N : ℕ → ℕ) : dyadicFirstFlagSign 0 B r N = 0 := by
  simp [dyadicFirstFlagSign, firstEventSign_eq_zero_iff]

example (d B : ℕ) (N : ℕ → ℕ) : dyadicFirstFlagSign d B 0 N = 0 := by
  simp [dyadicFirstFlagSign, firstEventSign_eq_zero_iff]

-- With precision zero no integer numerator enters the margin-1/4 flag window.
example : dyadicFirstFlagSign 4 0 3 id = 0 := by
  rw [dyadicFirstFlagSign, firstEventSign_eq_zero_iff]
  constructor <;> rintro ⟨k, hk, he, _⟩ <;> interval_cases k <;> norm_num at he

-- A flagged exact half is on neither strict side and is classified as zero.
example : dyadicFirstFlagSign 4 3 1 (fun _ => 4) = 0 := by
  rw [dyadicFirstFlagSign_eq_zero_iff (by decide)]
  constructor <;> rintro ⟨k, _, _, hside⟩ <;> norm_num at hside

example : (fun x : ℕ => dyadicFirstFlagSign 4 x x id) ∈
    CountingFunction 2 encUnary encIntBin := by
  apply CountingFunction.dyadicFirstFlagSign_mem (a := 0) Decoder.unary
    (N := Prod.snd) (d := fun _ => 4) (B := id) (r := id)
  · exact CountingFunction.of_polyTime (ComputableInPolyTime.snd _ _)
  · exact ComputableInPolyTime.const 4
  · exact ComputableInPolyTime.id'
  · exact ComputableInPolyTime.unary_to_binary
