/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive

/-! Tests of `enc_inductive`. -/

namespace CslibFrontierTests.InductiveEncoding

open Turing.MultiTapeTM

/-- A non-recursive inductive type with constructors of zero, one and two fields. -/
inductive Label where
  | resample
  | count (n : ℕ)
  | eval (u : ℕ) (y : List Bool)

enc_inductive eLabel : Label where
  | resample
  | count : encUnary
  | eval : encUnary, encBits

/-! The encoding unfolds to the summand of each constructor, and is injective. -/

example : eLabel .resample = [false] := by simp [eLabel_apply, eLabel_toSum]
example (n : ℕ) : eLabel (.count n) = true :: false :: encUnary n := by
  simp [eLabel_apply, eLabel_toSum]
example (u : ℕ) (y : List Bool) :
    eLabel (.eval u y) = true :: true :: encPair encUnary encBits (u, y) := by
  simp [eLabel_apply, eLabel_toSum]
example {x y : Label} (h : eLabel x = eLabel y) : x = y := eLabel.injective h

/-! Constructor rules compose with `fun_prop`. -/

example : ComputableInO (fun p : ℕ × List Bool => Label.eval p.1 p.2) (encPair encUnary encBits)
    eLabel (fun p => 2 * ((encPair encUnary encBits p).length + 1))
    fun p => 2 * ((encPair encUnary encBits p).length + 1) := by
  refine .mono (by fun_prop) 4 (fun p => ?_) fun p => ?_ <;>
  · simp only [length_encPair]
    omega

/-! Lifted constructor families cover captured arguments and independent workspace bounds. -/

example {α : Type} {enc : α ↪ List Bool} {u : α → ℕ} {v : α → List Bool}
    (hu : ComputableInPolyTime u enc encUnary) (hv : ComputableInPolyTime v enc encBits) :
    ComputableInPolyTime (fun a => Label.eval (u a) (v a)) enc eLabel :=
  eLabel_eval_polyTime hu hv

example {α : Type} {enc : α ↪ List Bool} {u : α → ℕ} {v : α → List Bool}
    {S₁ S₂ : α → ℕ} (hu : ComputableInSpace u enc encUnary S₁)
    (hv : ComputableInSpace v enc encBits S₂) :
    ComputableInSpace (fun a => Label.eval (u a) (v a)) enc eLabel (fun a => S₁ a + S₂ a) :=
  eLabel_eval_inSpace hu hv

example {α : Type} {enc : α ↪ List Bool} :
    ComputableInPolyTime (fun _ : α => Label.resample) enc eLabel := eLabel_resample_polyTime

example {α : Type} {enc : α ↪ List Bool} {u : α → ℕ}
    (hu : ComputableInPolyTime u enc encUnary) :
    ComputableInPolyTime (fun a => Label.count (u a)) enc eLabel := eLabel_count_polyTime hu

/-! Case analysis charges only the constructor taken. -/

/-- The size of a label's payload. -/
def weight (l : Label) : ℕ := eLabel_elim l (fun _ => 0) (fun n => n) (fun p => p.1)

example : weight (.eval 3 []) = 3 := rfl

example : ComputableInO (fun p : Unit × Label => eLabel_elim p.2 (fun _ => 0) (fun n => n)
      (fun q => q.1))
    (encPair encUnit eLabel) encUnary
    (fun p => 3 * (encPair encUnit eLabel p).length +
      eLabel_elim p.2 (fun _ => (encPair encUnit encUnit (p.1, ())).length)
        (fun n => (encPair encUnit encUnary (p.1, n)).length)
        (fun q => (encPair encUnit (encPair encUnary encBits) (p.1, q)).length))
    fun p => 3 * (encPair encUnit eLabel p).length +
      eLabel_elim p.2 (fun _ => (encPair encUnit encUnit (p.1, ())).length)
        (fun n => (encPair encUnit encUnary (p.1, n)).length)
        (fun q => (encPair encUnit (encPair encUnary encBits) (p.1, q)).length) :=
  eLabel_elim_inO (ComputableInO.const 0) (ComputableInDegree.snd encUnit encUnary).inO_one
    ((ComputableInDegree.snd encUnit (encPair encUnary encBits)).fst').inO_one

/-! An enumeration. -/

inductive Color where
  | red | green | blue

enc_inductive eColor : Color where
  | red
  | green
  | blue

example : eColor .blue = [true, true] := by simp [eColor_apply, eColor_toSum]

/-! A single constructor: no sum tag, and the payload is the encoding. -/

inductive Wrap where
  | wrap (n : ℕ) (b : Bool)

enc_inductive eWrap : Wrap where
  | wrap : encUnary, encBool

example (n : ℕ) (b : Bool) : eWrap (.wrap n b) = encPair encUnary encBool (n, b) := by
  simp [eWrap_apply, eWrap_toSum]

example : ComputableInO (fun p : ℕ × Bool => Wrap.wrap p.1 p.2) (encPair encUnary encBool) eWrap
    (fun p => 2 * ((encPair encUnary encBool p).length + 1))
    fun p => 2 * ((encPair encUnary encBool p).length + 1) := by
  refine .mono (by fun_prop) 4 (fun p => ?_) fun p => ?_ <;>
  · simp only [length_encPair]
    omega

example : ComputableInO (fun p : Unit × Wrap => eWrap_elim p.2 fun q => q.1)
    (encPair encUnit eWrap) encUnary
    (fun p => 1 * (encPair encUnit eWrap p).length +
      eWrap_elim p.2 fun q => (encPair encUnit (encPair encUnary encBool) (p.1, q)).length)
    fun p => 1 * (encPair encUnit eWrap p).length +
      eWrap_elim p.2 fun q => (encPair encUnit (encPair encUnary encBool) (p.1, q)).length :=
  eWrap_elim_inO ((ComputableInDegree.snd encUnit (encPair encUnary encBool)).fst').inO_one

/-! Single-constructor generation keeps both resource witnesses and all captured inputs. -/

example {α : Type} {enc : α ↪ List Bool} {u : α → ℕ} {v : α → Bool}
    (hu : ComputableInPolyTime u enc encUnary) (hv : ComputableInPolyTime v enc encBool) :
    ComputableInPolyTime (fun a => Wrap.wrap (u a) (v a)) enc eWrap :=
  eWrap_wrap_polyTime hu hv

example {ε π : Type} {encP : π ↪ List Bool} {encE : ε ↪ List Bool}
    {g : π × (ℕ × Bool) → ε} {S : π × (ℕ × Bool) → ℕ}
    (h : ComputableInSpace g (encPair encP (encPair encUnary encBool)) encE S) :
    ComputableInSpace (fun p : π × Wrap => eWrap_elim p.2 fun a => g (p.1, a))
      (encPair encP eWrap) encE
      (fun p => 1 * (encPair encP eWrap p).length + eWrap_elim p.2 fun a => S (p.1, a)) :=
  eWrap_elim_inSpace h

/-! Polynomial elimination keeps captured inputs and permits unrelated branch degrees. -/

example {π ε : Type} {encP : π ↪ List Bool} {encE : ε ↪ List Bool}
    {f : π × Unit → ε} {g : π × ℕ → ε} {h : π × (ℕ × List Bool) → ε}
    (hf : ComputableInPolyTime f (encPair encP encUnit) encE)
    (hg : ComputableInPolyTime g (encPair encP encUnary) encE)
    (hh : ComputableInPolyTime h (encPair encP (encPair encUnary encBits)) encE) :
    ComputableInPolyTime (fun p : π × Label =>
      eLabel_elim p.2 (fun a => f (p.1, a)) (fun a => g (p.1, a)) (fun a => h (p.1, a)))
      (encPair encP eLabel) encE :=
  eLabel_elim_polyTime hf hg hh

example {π ε : Type} {encP : π ↪ List Bool} {encE : ε ↪ List Bool}
    {g : π × (ℕ × Bool) → ε}
    (h : ComputableInPolyTime g (encPair encP (encPair encUnary encBool)) encE) :
    ComputableInPolyTime (fun p : π × Wrap => eWrap_elim p.2 fun a => g (p.1, a))
      (encPair encP eWrap) encE := eWrap_elim_polyTime h

/-! Matcher and projection clients distinguish empty payloads from absent constructors. -/

example : eLabel_resample_matches .resample = true := rfl
example : eLabel_count_matches (.eval 0 []) = false := rfl
example : eLabel_eval_payload? (.eval 0 []) = some (0, []) := rfl
example : eLabel_eval_field1? (.eval 0 []) = some [] := rfl
example : eLabel_eval_field1? .resample = none := rfl
example : eColor_blue_payload? .blue = some () := rfl
example : eWrap_wrap_field1? (.wrap 0 false) = some false := rfl

example : ComputableInDegree eLabel_count_matches eLabel encBool 1 0 := by fun_prop
example : ComputableInDegree eLabel_eval_field1? eLabel (encOption encBits) 1 1 := by fun_prop
example : ComputableInSpace eLabel_eval_payload? eLabel
    (encOption (encPair encUnary encBits)) (fun v => (eLabel v).length) := by fun_prop
example : ComputableInPolyTime (fun p : Unit × Label => eLabel_eval_field1? p.2)
    (encPair encUnit eLabel) (encOption encBits) :=
  eLabel_eval_field1?_polyTime.comp (ComputableInDegree.snd encUnit eLabel).computableInPolyTime

/-! Hosted transition probe. Keep registration local: existential resource/output degrees
must be found by automation before changing the global rule set. The explicit lift is the control.
Both paths retain arbitrary, independent degrees, including degree zero. -/

section DegreeTransitionProbe

variable {α β : Type} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}
  {d e : ℕ}

example (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := h.computableInPolyTime

attribute [local fun_prop] ComputableInDegree.computableInPolyTime

example (h : ComputableInDegree f encIn encOut d e) :
    ComputableInPolyTime f encIn encOut := by fun_prop

end DegreeTransitionProbe

/-! Mistakes in the constructor list are reported before anything is declared. -/

/--
error: enc_inductive: list every constructor of `Label` once, in declaration order:
  | resample | count | eval
-/
#guard_msgs in
enc_inductive eLabelOrder : Label where
  | count : encUnary
  | resample
  | eval : encUnary, encBits

/--
error: enc_inductive: `Label.eval` has 2 explicit field(s), but 1 encoding(s) are listed; give one
  encoding per field, in order
-/
#guard_msgs (whitespace := lax) in
enc_inductive eLabelFields : Label where
  | resample
  | count : encUnary
  | eval : encUnary

/--
error: Type mismatch
  encBits
has type
  List Bool ↪ List Bool
but is expected to have type
  ℕ ↪ List Bool
-/
#guard_msgs in
enc_inductive eLabelType : Label where
  | resample
  | count : encBits
  | eval : encUnary, encBits

/-- A type abbreviation, which is not an inductive type. -/
def Flag := Bool

/--
error: enc_inductive: `Flag` is not an inductive type
-/
#guard_msgs in
enc_inductive eFlag : Flag where
  | false
  | true

/-- A constructor with an implicit field. -/
inductive Tagged where
  | tag {n : ℕ} (b : Bool)

/--
error: enc_inductive: `Tagged.tag` has an implicit or instance field, which is not supported
-/
#guard_msgs in
enc_inductive eTagged : Tagged where
  | tag : encBool

/--
error: enc_inductive: `Option` has parameters or indices, which are not supported
-/
#guard_msgs in
enc_inductive eOption : Option where
  | none
  | some : encUnary

end CslibFrontierTests.InductiveEncoding
