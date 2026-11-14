/-
Copyright (c) 2026 Evelyn Mitchell, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evelyn Mitchell, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.SQL.Expr

/-!
# Typing and safety of SQL expressions

`UnOp.typeOf` and `BinOp.typeOf` give the result type of an operator on operands of given types,
and `Expr.typeOf Γ e` the type of an expression over a typing context `Γ : Fin n → SqlType`: a
literal has its value's type, `NULL` its declared type, `col i` the type `Γ i`, `e IN vs` is
boolean when every list element has `e`'s type, and `CASE` needs a boolean condition and branches
of one type.

Type soundness (`Expr.eval_ok_or_divisionByZero`): on a row conforming to `Γ`, a well-typed
expression of type `τ` never raises `typeMismatch`; it either returns `NULL` or a value of type
`τ`, or divides by zero. Division by zero is excluded syntactically by `Expr.divSafe`: `/` and `%`
only by a nonzero integer literal. An expression is *safe* (`Expr.IsSafe`, decidable) when it is
well-typed and `divSafe`, and a safe expression succeeds on every conforming row
(`Expr.IsSafe.exists_eval_eq_ok`). A safe predicate (`Expr.IsSafePredicate`, also boolean-typed)
never makes a `WHERE` or `ON` clause fail. Laws that move, duplicate or drop the evaluation of an
expression use safety as their side condition. A divisor that is a column or a computed expression
is not safe even when it is never zero on the data: safety is a syntactic check.

Typing and safety are preserved by renaming and by substitution of safe expressions of the right
types (`Expr.typeOf_rename`, `Expr.typeOf_subst`, `Expr.IsSafe.rename`,
`Expr.IsSafePredicate.rename`, `Expr.IsSafe.subst`).

It adapts and redesigns the typing of `sql_equiv` (revision `38030a6b`) by Evelyn Mitchell, whose
type checks came from the data at evaluation time; here typing is static, relative to a typing
context.

## Main definitions

* `Cslib.SQL.UnOp.typeOf`, `Cslib.SQL.BinOp.typeOf`: result types of the operators.
* `Cslib.SQL.Expr.typeOf`: the type of an expression in a typing context.
* `Cslib.SQL.Expr.divSafe`: every division or remainder is by a nonzero integer literal.
* `Cslib.SQL.Expr.IsSafe`, `Cslib.SQL.Expr.IsSafePredicate`: the decidable safety checks.

## Main results

* `Cslib.SQL.evalUnOp_ok_of_typeOf`, `Cslib.SQL.evalBinOp_ok_or_divisionByZero`: operator
  soundness.
* `Cslib.SQL.Expr.eval_ok_or_divisionByZero`, `Cslib.SQL.Expr.eval_spec`: type soundness of
  expressions, also as a postcondition that composes along evaluation.
* `Cslib.SQL.Expr.eval_ne_typeMismatch`: a well-typed expression never raises a type error.
* `Cslib.SQL.Expr.IsSafe.exists_eval_eq_ok`: a safe expression succeeds on conforming rows.
* `Cslib.SQL.Expr.IsSafePredicate.exists_evalTruth_eq_ok`: a safe predicate never fails.
-/

@[expose] public section

namespace Cslib.SQL

/-! ### Operators -/

/-- The result type of a unary operator on an operand of type `τ`, if the application is
well-typed. -/
def UnOp.typeOf : UnOp → SqlType → Option SqlType
  | .not, .bool => some .bool
  | .neg, .int => some .int
  | .isNull, _ => some .bool
  | .isNotNull, _ => some .bool
  | _, _ => none

/-- The result type of a binary operator on operands of types `τ₁` and `τ₂`, if the application is
well-typed: comparisons need equal types. -/
def BinOp.typeOf : BinOp → SqlType → SqlType → Option SqlType
  | .arith _, .int, .int => some .int
  | .cmp _, τ₁, τ₂ => if τ₁ = τ₂ then some .bool else none
  | .and, .bool, .bool => some .bool
  | .or, .bool, .bool => some .bool
  | .concat, .text, .text => some .text
  | _, _, _ => none

/-- Whether the operator fails on a zero divisor: `/` and `%`. -/
def BinOp.isDivision : BinOp → Bool
  | .arith op => op.isDivision
  | _ => false

/-- A well-typed unary operator succeeds, with a result of its type. -/
theorem evalUnOp_ok_of_typeOf {op : UnOp} {τ τ' : SqlType} (h : op.typeOf τ = some τ')
    {d : Datum} (hd : d.HasType τ) : ∃ d', evalUnOp op d = .ok d' ∧ d'.HasType τ' := by
  match op, τ, h with
  | .not, .bool, h =>
    cases h
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
    exact ⟨t.not.toDatum, by simp [evalUnOp, ht], Truth.toDatum_hasType _⟩
  | .neg, .int, h =>
    cases h
    obtain ⟨x, hx⟩ := Datum.exists_asInt_eq_ok_iff.mpr hd
    refine ⟨x.map fun z => .int (negInt z), by simp [evalUnOp, hx], ?_⟩
    cases x <;> simp
  | .isNull, _, h => cases h; exact ⟨_, rfl, rfl⟩
  | .isNotNull, _, h => cases h; exact ⟨_, rfl, rfl⟩

/-- A well-typed binary operator succeeds with a result of its type, unless it divides by zero,
in which case the divisor is the integer `0`. -/
theorem evalBinOp_ok_or_divisionByZero {op : BinOp} {τ₁ τ₂ τ : SqlType}
    (h : op.typeOf τ₁ τ₂ = some τ) {a b : Datum} (ha : a.HasType τ₁) (hb : b.HasType τ₂) :
    (∃ d, evalBinOp op a b = .ok d ∧ d.HasType τ) ∨
      (evalBinOp op a b = .error .divisionByZero ∧ op.isDivision ∧ b = some (.int 0)) := by
  match op, τ₁, τ₂, h with
  | .arith op, .int, .int, h =>
    cases h
    obtain ⟨x, hx⟩ := Datum.exists_asInt_eq_ok_iff.mpr ha
    obtain ⟨y, hy⟩ := Datum.exists_asInt_eq_ok_iff.mpr hb
    rcases x with _ | x <;> rcases y with _ | y
    case some.some =>
      rcases hz : op.eval x y with e | z
      · obtain ⟨rfl, hd, rfl⟩ := ArithOp.eval_eq_error hz
        exact .inr ⟨by simp [evalBinOp, hx, hy, hz], hd, Datum.asInt_eq_ok_some_iff.mp hy⟩
      · exact .inl ⟨some (.int z), by simp [evalBinOp, hx, hy, hz], rfl⟩
    all_goals exact .inl ⟨none, by simp [evalBinOp, hx, hy], trivial⟩
  | .cmp op, τ₁, τ₂, h =>
    simp only [BinOp.typeOf, Option.ite_none_right_eq_some, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨t, ht⟩ := CmpOp.exists_eval_eq_ok (op := op) ha hb
    exact .inl ⟨t.toDatum, by simp [evalBinOp, ht], Truth.toDatum_hasType _⟩
  | .and, .bool, .bool, h =>
    cases h
    obtain ⟨s, hs⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hb
    exact .inl ⟨(s ⊓ t).toDatum, by simp [evalBinOp, hs, ht], Truth.toDatum_hasType _⟩
  | .or, .bool, .bool, h =>
    cases h
    obtain ⟨s, hs⟩ := Datum.exists_toTruth_eq_ok_iff.mpr ha
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hb
    exact .inl ⟨(s ⊔ t).toDatum, by simp [evalBinOp, hs, ht], Truth.toDatum_hasType _⟩
  | .concat, .text, .text, h =>
    cases h
    obtain ⟨x, hx⟩ := Datum.exists_asText_eq_ok_iff.mpr ha
    obtain ⟨y, hy⟩ := Datum.exists_asText_eq_ok_iff.mpr hb
    rcases x with _ | x <;> rcases y with _ | y
    case some.some =>
      refine .inl ⟨some (.text (concatText x y)), ?_, rfl⟩
      simp [evalBinOp, hx, hy]
    all_goals exact .inl ⟨none, by simp [evalBinOp, hx, hy], trivial⟩

namespace Expr

variable {n m : ℕ}

/-! ### Expressions -/

/-- The type of an expression over the typing context `Γ`, if it is well-typed. -/
def typeOf (Γ : Fin n → SqlType) : Expr n → Option SqlType
  | lit v => some v.type
  | null τ => some τ
  | col i => some (Γ i)
  | unary op e => do op.typeOf (← e.typeOf Γ)
  | binary op e₁ e₂ => do op.typeOf (← e₁.typeOf Γ) (← e₂.typeOf Γ)
  | inList e vs => do
    let τ ← e.typeOf Γ
    if vs.all fun v => decide (v.HasType τ) then some .bool else none
  | caseWhen c a b => do
    let τ ← a.typeOf Γ
    if c.typeOf Γ = some .bool ∧ b.typeOf Γ = some τ then some τ else none

/-- The expression is an integer literal other than `0`. -/
def isNonzeroIntLit : Expr n → Bool
  | lit (.int z) => z != 0
  | _ => false

/-- Every division and remainder in the expression is by a nonzero integer literal. -/
def divSafe : Expr n → Bool
  | lit _ => true
  | null _ => true
  | col _ => true
  | unary _ e => e.divSafe
  | binary op e₁ e₂ => (!op.isDivision || e₂.isNonzeroIntLit) && e₁.divSafe && e₂.divSafe
  | inList e _ => e.divSafe
  | caseWhen c a b => c.divSafe && a.divSafe && b.divSafe

/-- The expression is well-typed in `Γ` and every division is by a nonzero literal; then it
succeeds on every row conforming to `Γ` (`Expr.IsSafe.exists_eval_eq_ok`). -/
def IsSafe (Γ : Fin n → SqlType) (e : Expr n) : Prop :=
  (e.typeOf Γ).isSome ∧ e.divSafe

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsSafe Γ) :=
  inferInstanceAs (Decidable ((e.typeOf Γ).isSome ∧ e.divSafe))

/-- The expression is a safe boolean predicate in `Γ`; then a `WHERE` or `ON` clause using it
never fails on a row conforming to `Γ` (`Expr.IsSafePredicate.exists_evalTruth_eq_ok`). -/
def IsSafePredicate (Γ : Fin n → SqlType) (e : Expr n) : Prop :=
  e.typeOf Γ = some .bool ∧ e.divSafe

instance (Γ : Fin n → SqlType) (e : Expr n) : Decidable (e.IsSafePredicate Γ) :=
  inferInstanceAs (Decidable (e.typeOf Γ = some .bool ∧ e.divSafe))

private theorem eval_ne_ok_zero_of_isNonzeroIntLit {e : Expr n} (he : e.isNonzeroIntLit)
    (r : Row n) : e.eval r ≠ .ok (some (.int 0)) := by
  match e, he with
  | lit (.int z), he =>
    simp only [isNonzeroIntLit, bne_iff_ne, ne_eq] at he
    simpa using he

/-- Type soundness as a postcondition: on a row conforming to `Γ`, an expression of type `τ`
returns `NULL` or a value of type `τ`, or divides by zero, which requires a division that is not
`divSafe`. -/
theorem eval_spec {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ) {e : Expr n}
    {τ : SqlType} (he : e.typeOf Γ = some τ) :
    (e.eval r).Spec (·.HasType τ) fun err => err = .divisionByZero ∧ e.divSafe = false := by
  induction e generalizing τ with
  | lit v => cases he; rfl
  | null σ => cases he; trivial
  | col i => cases he; exact hr i
  | unary op e ih =>
    obtain ⟨τ₀, h₀, hop⟩ := Option.bind_eq_some_iff.mp he
    refine ((ih h₀).imp_error fun hs => by simp [divSafe, hs]).bind
      fun d _ hd => ?_
    obtain ⟨d', hd', hd'τ⟩ := evalUnOp_ok_of_typeOf hop hd
    simpa [hd'] using hd'τ
  | binary op e₁ e₂ ih₁ ih₂ =>
    obtain ⟨τ₁, h₁, he⟩ := Option.bind_eq_some_iff.mp he
    obtain ⟨τ₂, h₂, hop⟩ := Option.bind_eq_some_iff.mp he
    refine ((ih₁ h₁).imp_error fun hs => by simp [divSafe, hs]).bind
      fun a _ ha => ((ih₂ h₂).imp_error fun hs => by simp [divSafe, hs]).bind
      fun b hb hbτ => ?_
    rcases evalBinOp_ok_or_divisionByZero hop ha hbτ with ⟨d, hd, hdτ⟩ | ⟨hd, hdiv, rfl⟩
    · simpa [hd] using hdτ
    · have hlit : e₂.isNonzeroIntLit = false := by
        by_contra hlit
        exact eval_ne_ok_zero_of_isNonzeroIntLit (Bool.eq_true_of_not_eq_false hlit) r hb
      simp [hd, divSafe, hdiv, hlit]
  | inList e vs ih =>
    obtain ⟨τ₀, h₀, hvs⟩ := Option.bind_eq_some_iff.mp he
    split_ifs at hvs with hall
    cases hvs
    refine ((ih h₀).imp_error fun hs => by simp [divSafe, hs]).bind
      fun d _ hd => ?_
    obtain ⟨t, ht⟩ := Datum.exists_inList_eq_ok hd (by simpa using hall)
    simp [ht]
  | caseWhen c a b ihc iha ihb =>
    obtain ⟨τ₀, ha, hcb⟩ := Option.bind_eq_some_iff.mp he
    split_ifs at hcb with hcond
    cases hcb
    refine ((ihc hcond.1).imp_error fun hs => by simp [divSafe, hs]).bind
      fun d _ hd => ?_
    obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hd
    rw [ht, Except.ok_bind]
    split
    · exact (iha ha).imp_error fun hs => by simp [divSafe, hs]
    · exact (ihb hcond.2).imp_error fun hs => by simp [divSafe, hs]

/-- Type soundness: on a row conforming to `Γ`, an expression of type `τ` returns `NULL` or a
value of type `τ`, or divides by zero, which requires a division that is not `divSafe`. -/
theorem eval_ok_or_divisionByZero {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) :
    (∃ d, e.eval r = .ok d ∧ d.HasType τ) ∨
      (e.eval r = .error .divisionByZero ∧ e.divSafe = false) :=
  (eval_spec hr he).eq_ok_or_eq_error

/-- A well-typed expression never raises a type error on a conforming row. -/
theorem eval_ne_typeMismatch {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) : e.eval r ≠ .error .typeMismatch :=
  (eval_spec hr he).ne_error (by simp)

/-- The result of a well-typed expression on a conforming row has the expression's type. -/
theorem hasType_of_eval_eq_ok {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) {d : Datum} (h : e.eval r = .ok d) :
    d.HasType τ :=
  (eval_spec hr he).of_eq_ok h

/-- A well-typed `divSafe` expression succeeds on a conforming row, with a result of its type. -/
theorem exists_eval_eq_ok_of_divSafe {Γ : Fin n → SqlType} {r : Row n} (hr : r.Conforms Γ)
    {e : Expr n} {τ : SqlType} (he : e.typeOf Γ = some τ) (hs : e.divSafe) :
    ∃ d, e.eval r = .ok d ∧ d.HasType τ :=
  (eval_spec hr he).exists_eq_ok (by simp [hs])

/-- A safe expression succeeds on every conforming row. -/
theorem IsSafe.exists_eval_eq_ok {Γ : Fin n → SqlType} {e : Expr n} (hs : e.IsSafe Γ)
    {r : Row n} (hr : r.Conforms Γ) : ∃ d, e.eval r = .ok d := by
  obtain ⟨τ, hτ⟩ := Option.isSome_iff_exists.mp hs.1
  obtain ⟨d, hd, -⟩ := exists_eval_eq_ok_of_divSafe hr hτ hs.2
  exact ⟨d, hd⟩

theorem IsSafePredicate.isSafe {Γ : Fin n → SqlType} {e : Expr n} (h : e.IsSafePredicate Γ) :
    e.IsSafe Γ :=
  ⟨by simp [h.1], h.2⟩

/-- A safe predicate never fails on a conforming row, so a `WHERE` or `ON` clause using it is
total. -/
theorem IsSafePredicate.exists_evalTruth_eq_ok {Γ : Fin n → SqlType} {e : Expr n}
    (h : e.IsSafePredicate Γ) {r : Row n} (hr : r.Conforms Γ) : ∃ t, e.evalTruth r = .ok t := by
  obtain ⟨d, hd, hdτ⟩ := exists_eval_eq_ok_of_divSafe hr h.1 h.2
  obtain ⟨t, ht⟩ := Datum.exists_toTruth_eq_ok_iff.mpr hdτ
  exact ⟨t, by simp [evalTruth, hd, ht]⟩

/-! ### Renaming and substitution -/

theorem typeOf_rename (ρ : Fin n → Fin m) (Γ : Fin m → SqlType) (e : Expr n) :
    (e.rename ρ).typeOf Γ = e.typeOf (Γ ∘ ρ) := by
  induction e <;> simp_all [rename, typeOf]

/-- Substituting expressions of the column types preserves the type. -/
theorem typeOf_subst {σ : Fin n → Expr m} {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    (hσ : ∀ i, (σ i).typeOf Δ = some (Γ i)) (e : Expr n) : (e.subst σ).typeOf Δ = e.typeOf Γ := by
  induction e <;> simp_all [subst, typeOf]

@[simp] theorem divSafe_rename (ρ : Fin n → Fin m) (e : Expr n) :
    (e.rename ρ).divSafe = e.divSafe := by
  have hlit : ∀ e : Expr n, (e.rename ρ).isNonzeroIntLit = e.isNonzeroIntLit := by
    intro e
    cases e with
    | lit v => cases v <;> rfl
    | _ => rfl
  induction e <;> simp_all [rename, divSafe]

/-- Substituting `divSafe` expressions into a `divSafe` expression keeps it `divSafe`. -/
theorem divSafe_subst {σ : Fin n → Expr m} (hσ : ∀ i, (σ i).divSafe) {e : Expr n}
    (he : e.divSafe) : (e.subst σ).divSafe := by
  have hlit : ∀ e : Expr n, e.isNonzeroIntLit → (e.subst σ).isNonzeroIntLit := by
    intro e h
    match e, h with
    | lit (.int _), h => exact h
  induction e with
  | lit | null | col => simp_all [subst, divSafe]
  | unary op e ih => simp_all [subst, divSafe]
  | binary op e₁ e₂ ih₁ ih₂ =>
    simp only [divSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true] at he
    obtain ⟨⟨hdiv, h₁⟩, h₂⟩ := he
    simp only [subst, divSafe, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
      Bool.not_true, ih₁ h₁, ih₂ h₂, and_true]
    exact hdiv.imp_right (hlit e₂)
  | inList e vs ih => simp_all [subst, divSafe]
  | caseWhen c a b ihc iha ihb => simp_all [subst, divSafe]

theorem IsSafe.rename {Γ : Fin m → SqlType} {e : Expr n} (ρ : Fin n → Fin m)
    (h : e.IsSafe (Γ ∘ ρ)) : (e.rename ρ).IsSafe Γ := by
  simpa [IsSafe, typeOf_rename] using h

theorem IsSafePredicate.rename {Γ : Fin m → SqlType} {e : Expr n} (ρ : Fin n → Fin m)
    (h : e.IsSafePredicate (Γ ∘ ρ)) : (e.rename ρ).IsSafePredicate Γ := by
  simpa [IsSafePredicate, typeOf_rename] using h

/-- Substituting safe expressions of the column types into a safe expression keeps it safe. -/
theorem IsSafe.subst {σ : Fin n → Expr m} {Γ : Fin n → SqlType} {Δ : Fin m → SqlType}
    (hσ : ∀ i, (σ i).typeOf Δ = some (Γ i)) (hσs : ∀ i, (σ i).divSafe) {e : Expr n}
    (h : e.IsSafe Γ) : (e.subst σ).IsSafe Δ :=
  ⟨by rw [typeOf_subst hσ]; exact h.1, divSafe_subst hσs h.2⟩

end Expr

end Cslib.SQL
