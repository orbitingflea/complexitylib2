/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition

/-! # Direct degree bounds from encoding capabilities

Identity, pair projections and framed-list operations reuse the encoding capabilities.
Computed projections retain independent resource and output degrees through plain composition.
-/

public section
namespace Turing.MultiTapeTM.ComputableInDegree
universe u

/-- The first component of a standard framed pair. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.fst (encPair enc₁ enc₂) enc₁ 1 1 := PairEncoding.fst enc₂

/-- The second component of a standard framed pair. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.snd (encPair enc₁ enc₂) enc₂ 1 1 := PairEncoding.snd enc₁

variable {d₁ e₁ d₂ e₂ : ℕ}

/-- Framed pairing retains the independent encoded-output degrees. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (max d₁ d₂)
      (max e₁ e₂) :=
  ⟨(hf.pair hg).1, (((hf.2.smul 2).add_const 1).add_max hg.2).mono fun x => by simp⟩

/-- Adding an element in front of a framed list: the identity on encoded words. -/
theorem cons {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : α × List α => p.1 :: p.2) (encPair enc (encList enc))
      (encList enc) 1 1 :=
  of_eq fun _ => rfl

/-- The result encoding fixes the element encoding, without reversing `ListEncoding` inference. -/
@[fun_prop]
theorem listTail {α : Type*} (enc : α ↪ List Bool) :
    ComputableInDegree List.tail (encList enc) (encList enc) 1 1 :=
  ListEncoding.tail (enc₁ := enc)

/-- The framed input list determines the encoding of its head, including a fixed fallback. -/
@[fun_prop]
theorem listHeadD {α : Type*} (enc : α ↪ List Bool) (fallback : α) :
    ComputableInDegree (fun l => l.headD fallback) (encList enc) enc 1 1 :=
  ListEncoding.headD (enc₁ := enc) fallback

/-- The first component of a pair computed with given degrees.
The input universe is independent of the pair's universe. -/
theorem fst' {α : Type*} {β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {d e : ℕ}
    {f : α → β₁ × β₂} (h : ComputableInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableInDegree (fun x => (f x).1) encIn enc₁ (max d e) e :=
  ((fst enc₁ enc₂).comp h).mono

/-- The second component of a pair computed with given degrees.
The input universe is independent of the pair's universe. -/
theorem snd' {α : Type*} {β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} {d e : ℕ}
    {f : α → β₁ × β₂} (h : ComputableInDegree f encIn (encPair enc₁ enc₂) d e) :
    ComputableInDegree (fun x => (f x).2) encIn enc₂ (max d e) e :=
  ((snd enc₁ enc₂).comp h).mono

/-- `List.headD` on any list encoding. -/
theorem headD {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] (d : β) :
    ComputableInDegree (fun l => l.headD d) enc enc₁ 1 1 :=
  ListEncoding.headD d

/-- `List.tail` on any list encoding. -/
theorem tail {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] :
    ComputableInDegree List.tail enc enc 1 1 :=
  ListEncoding.tail (enc₁ := enc₁)

/-- `List.isEmpty` on any list encoding. -/
theorem isEmpty {β : Type*} {enc₁ : β ↪ List Bool} {enc : List β ↪ List Bool}
    [ListEncoding enc₁ enc] :
    ComputableInDegree List.isEmpty enc encBool 1 1 :=
  ListEncoding.isEmpty (enc₁ := enc₁)

/-- Adding an element at the end of a framed list. -/
theorem snoc {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × α => p.1 ++ [p.2]) (encPair (encList enc) enc)
      (encList enc) 1 1 :=
  ((fst (encList enc) enc).append ((ComputableInDegree.of_frame (f := id) (encIn := enc)
      (encMid := encFramed enc) fun _ => rfl).comp (snd (encList enc) enc))
    (enc₂ := encFramed enc) fun _ => by simp).mono

/-- Concatenating two framed lists. -/
theorem listAppend {α : Type} (enc : α ↪ List Bool) :
    ComputableInDegree (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) 1 1 :=
  ((fst (encList enc) (encList enc)).append (snd (encList enc) (encList enc))
    fun _ => by simp).mono

/-- Copy an encoded value. This identity rule also lets `fun_prop` retain a shared let binding. -/
@[fun_prop]
theorem id' {α : Type*} {enc : α ↪ List Bool} :
    ComputableInDegree (fun x : α => x) enc enc 1 1 :=
  of_eq fun _ => rfl

end Turing.MultiTapeTM.ComputableInDegree
