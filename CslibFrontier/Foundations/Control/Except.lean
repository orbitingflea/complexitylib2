/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate (Batteries, `Batteries/Data/Except.lean`)

public import CslibFrontier.Init
import Batteries.Data.List.Lemmas

/-!
# Sequencing and observing `Except`

Core and Batteries state how `<$>` acts on `Except.ok` and `Except.error`, but not `>>=`, and
nothing about `Except.toOption`, which forgets which error occurred. These equations let `simp`
evaluate `do` blocks over `Except` and compare computations up to the error they raise.

For a list of computations run from left to right, `List.mapM` and `List.filterMapM` succeed
exactly when every step does, and then return the results of the steps. Batteries characterizes
the successful results of `List.mapM` by `List.Forall₂` (`List.mapM_eq_ok_iff_forall₂`); the
observations here say the same through `Except.toOption`, in a form that is stable under
permutations and filters of the list.

A specification `x.Spec P E` says that `x` succeeds with a result satisfying `P` or fails with an
error satisfying `E`. Specifications of the steps of a `do` block compose by `Except.Spec.bind`,
so a proof that a program only fails in a given way needs no case for each step that can fail.

## Main results

* `Except.ok_bind`, `Except.error_bind`: `>>=` on a result and on an error.
* `Except.bind_eq_ok`: a sequenced computation succeeds when both steps do.
* `Except.toOption_bind`, `Except.toOption_map`: observing success commutes with sequencing.
* `Except.toOption_eq_some_iff`: an observed success is a success.
* `Except.toOption_mapM`, `Except.toOption_filterMapM`: the observation of a list of
  computations.
* `Except.mapM_eq_ok_map`, `Except.toOption_mapM_congr`: `List.mapM` of succeeding steps, and of
  steps with the same observations.
* `Except.Spec`, `Except.Spec.bind`: a computation succeeds with a result satisfying `P` or fails
  with an error satisfying `E`, and such specifications compose along `>>=`.
* `Except.Spec.mapM`, `Except.Spec.filterMapM`: the results of a successful list of computations
  come from steps meeting their specifications.
-/

public section

namespace Except

universe u v

variable {ε : Type u} {α β : Type v}

@[simp] theorem ok_bind (a : α) (f : α → Except ε β) : (Except.ok a >>= f) = f a := rfl

@[simp] theorem error_bind (e : ε) (f : α → Except ε β) : (Except.error e >>= f) = .error e := rfl

/-- `pure` is `Except.ok`. The simp normal form is `Except.ok`, the form statements use. -/
@[simp] theorem pure_eq_ok (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- Continuing with `Except.ok` returns the computation: the right unit law in the normal form
of `Except.pure_eq_ok`. -/
@[simp] theorem bind_ok (x : Except ε α) : x >>= Except.ok = x := by
  cases x <;> rfl

theorem bind_eq_ok {x : Except ε α} {f : α → Except ε β} {b : β} :
    x >>= f = .ok b ↔ ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x <;> simp

/-- Computations that can fail only with the same error commute. -/
theorem bind_comm_of_eq_error {γ : Type v} {x : Except ε α} {y : Except ε β} {e₀ : ε}
    (hx : ∀ e, x = .error e → e = e₀) (hy : ∀ e, y = .error e → e = e₀)
    (f : α → β → Except ε γ) :
    (x >>= fun a => y >>= fun b => f a b) = (y >>= fun b => x >>= fun a => f a b) := by
  rcases hx' : x with e | a <;> rcases hy' : y with e' | b
  · rw [hx e hx', hy e' hy']; rfl
  all_goals rfl

@[simp] theorem toOption_ok (a : α) : (Except.ok a : Except ε α).toOption = some a := rfl

@[simp] theorem toOption_error (e : ε) : (Except.error e : Except ε α).toOption = none := rfl

theorem toOption_pure (a : α) : (pure a : Except ε α).toOption = some a := rfl

theorem toOption_bind (x : Except ε α) (f : α → Except ε β) :
    (x >>= f).toOption = x.toOption.bind fun a => (f a).toOption := by
  cases x <;> rfl

theorem toOption_map (f : α → β) (x : Except ε α) : (f <$> x).toOption = f <$> x.toOption := by
  cases x <;> rfl

theorem toOption_eq_some_iff {x : Except ε α} {a : α} : x.toOption = some a ↔ x = .ok a := by
  cases x <;> simp [Except.toOption]

/-! ### Lists of computations -/

/-- `List.mapM` succeeds exactly when every step succeeds, and then returns their results. -/
theorem toOption_mapM (f : α → Except ε β) (l : List α) :
    (l.mapM f).toOption =
      if ∀ a ∈ l, (f a).toOption.isSome then some (l.filterMap fun a => (f a).toOption)
      else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases h : f a with e | b
    · simp [h]
    · simp only [List.mapM_cons, h, ok_bind, toOption_bind, ih]
      split_ifs <;> simp_all

/-- `List.mapM` of steps that succeed returns their results. -/
theorem mapM_eq_ok_map {f : α → Except ε β} {g : α → β} {l : List α}
    (h : ∀ a ∈ l, f a = .ok (g a)) : l.mapM f = .ok (l.map g) :=
  List.mapM_eq_ok_iff_forall₂.mpr <| by induction l <;> simp_all

/-- `List.mapM` of steps with the same observations on the list has the same observation. -/
theorem toOption_mapM_congr {f g : α → Except ε β} {l : List α}
    (h : ∀ a ∈ l, (f a).toOption = (g a).toOption) :
    (l.mapM f).toOption = (l.mapM g).toOption := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.mapM_cons, toOption_bind, h a List.mem_cons_self,
      ih fun b hb => h b (List.mem_cons_of_mem a hb)]

/-- `List.filterMapM` succeeds exactly when every step succeeds, and then keeps the present
results. -/
theorem toOption_filterMapM (f : α → Except ε (Option β)) (l : List α) :
    (l.filterMapM f).toOption =
      if ∀ a ∈ l, (f a).toOption.isSome then some (l.filterMap fun a => (f a).toOption.join)
      else none := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rcases h : f a with e | (_ | b)
    · simp [h]
    · simp only [List.filterMapM_cons, h, ok_bind]
      rw [ih]
      split_ifs <;> simp_all
    · simp only [List.filterMapM_cons, h, ok_bind, toOption_bind, ih]
      split_ifs <;> simp_all

/-! ### Postconditions -/

section Spec

variable {P P' : α → Prop} {Q : β → Prop} {E E' : ε → Prop}

/-- `x.Spec P E`: `x` succeeds with a result satisfying `P`, or fails with an error satisfying
`E`. Specifications of the steps of a `do` block compose by `Except.Spec.bind`. -/
@[expose] def Spec (P : α → Prop) (E : ε → Prop) : Except ε α → Prop
  | .ok a => P a
  | .error e => E e

@[simp] theorem spec_ok {a : α} : (Except.ok a : Except ε α).Spec P E ↔ P a := Iff.rfl

@[simp] theorem spec_error {e : ε} : (Except.error e : Except ε α).Spec P E ↔ E e := Iff.rfl

/-- A sequenced computation meets `Q` and `E` when its first step meets `P` and `E`, and the rest
meets `Q` and `E` from every result of the first step satisfying `P`. -/
theorem Spec.bind {x : Except ε α} {f : α → Except ε β} (hx : x.Spec P E)
    (hf : ∀ a, x = .ok a → P a → (f a).Spec Q E) : (x >>= f).Spec Q E := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a rfl hx

theorem Spec.mono {x : Except ε α} (hx : x.Spec P E) (hP : ∀ a, P a → P' a)
    (hE : ∀ e, E e → E' e) : x.Spec P' E' := by
  cases x with
  | error e => exact hE e hx
  | ok a => exact hP a hx

/-- Weaken the condition under which a computation fails with `e₀`. -/
theorem Spec.imp_error {x : Except ε α} {e₀ : ε} {B B' : Prop}
    (hx : x.Spec P fun e => e = e₀ ∧ B) (h : B → B') : x.Spec P fun e => e = e₀ ∧ B' :=
  hx.mono (fun _ => id) fun _ h' => ⟨h'.1, h h'.2⟩

theorem Spec.of_eq_ok {x : Except ε α} (hx : x.Spec P E) {a : α} (h : x = .ok a) : P a := by
  subst h; exact hx

theorem Spec.of_eq_error {x : Except ε α} (hx : x.Spec P E) {e : ε} (h : x = .error e) :
    E e := by
  subst h; exact hx

theorem Spec.ne_error {x : Except ε α} (hx : x.Spec P E) {e : ε} (he : ¬E e) :
    x ≠ .error e := by
  rintro rfl; exact he hx

theorem Spec.exists_eq_ok {x : Except ε α} (hx : x.Spec P E) (hE : ∀ e, ¬E e) :
    ∃ a, x = .ok a ∧ P a := by
  cases x with
  | error e => exact absurd hx (hE e)
  | ok a => exact ⟨a, rfl, hx⟩

/-- A computation that fails only with `e₀`, under the condition `B`. -/
theorem Spec.eq_ok_or_eq_error {x : Except ε α} {e₀ : ε} {B : Prop}
    (hx : x.Spec P fun e => e = e₀ ∧ B) : (∃ a, x = .ok a ∧ P a) ∨ (x = .error e₀ ∧ B) := by
  cases x with
  | error e => exact .inr ⟨congrArg error hx.1, hx.2⟩
  | ok a => exact .inl ⟨a, rfl, hx⟩

/-- Every result of a successful `List.mapM` comes from a step whose specification it meets. -/
theorem Spec.mapM {l : List α} {f : α → Except ε β} {R : α → β → Prop}
    (h : ∀ a ∈ l, (f a).Spec (R a) E) :
    (l.mapM f).Spec (fun bs => ∀ b ∈ bs, ∃ a ∈ l, R a b) E := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.mapM_cons]
    refine (h a List.mem_cons_self).bind fun b₀ _ hb₀ =>
      (ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')).bind fun bs _ hbs b hb => ?_
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ⟨a, List.mem_cons_self, hb₀⟩
    · exact (hbs b hb).imp fun _ ⟨h, h'⟩ => ⟨List.mem_cons_of_mem a h, h'⟩

/-- Every result of a successful `List.filterMapM` comes from a step whose specification it
meets. -/
theorem Spec.filterMapM {l : List α} {f : α → Except ε (Option β)} {R : α → β → Prop}
    (h : ∀ a ∈ l, (f a).Spec (fun o => ∀ b ∈ o, R a b) E) :
    (l.filterMapM f).Spec (fun bs => ∀ b ∈ bs, ∃ a ∈ l, R a b) E := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.filterMapM_cons]
    have ih' := ih fun a' ha' => h a' (List.mem_cons_of_mem a ha')
    have lift : ∀ bs : List β, (∀ b ∈ bs, ∃ a' ∈ l, R a' b) → ∀ b ∈ bs, ∃ a' ∈ a :: l, R a' b :=
      fun bs hbs b hb => (hbs b hb).imp fun _ ⟨h, h'⟩ => ⟨List.mem_cons_of_mem a h, h'⟩
    refine (h a List.mem_cons_self).bind fun o _ ho => ?_
    cases o with
    | none => exact ih'.mono lift fun _ => id
    | some b₀ =>
      refine ih'.bind fun bs _ hbs b hb => ?_
      rcases List.mem_cons.mp hb with rfl | hb
      · exact ⟨a, List.mem_cons_self, ho b rfl⟩
      · exact lift bs hbs b hb

end Spec

end Except
