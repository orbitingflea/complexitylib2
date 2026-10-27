/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger, Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger, Anton Kovsharov
-/

-- upstream: local-only (formal abstract library)

import ComplexityAbstracts.Check
import ComplexityAbstracts.Encoding
import ComplexityAbstracts.SubexponentialSATBridge
import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Fintype.Pi

/-! # OpenAI: the Exponential Time Hypothesis is false

The four theorems below are proved through `SubexponentialSATBridge` from the unconditional
native counting endpoint.

The primary result is one deterministic machine for each fixed clause width that computes the
number of satisfying assignments of every formula of that width. With `n` the number of distinct
variables, its running time is exponential in a constant times
`n (log log (n + 16))² / sqrt (log (n + 16))`, multiplied by a polynomial in the encoded formula
length. Its work space, including a separate charge for the encoded output, is polynomial in that
same length. This is the interpolation-scale route of Sections 3–6 and
Proposition 6.4 of [OpenAI2026ETH], not the sharper Theorem 1.1 / Appendix D bound.

The definitions here display the existing CNF semantics, encodings and fine-grained classes;
they are not alternative library interfaces. The accompanying regression module checks their
agreement with the canonical definitions. Machinery is existential. The bridge imports the
public unconditional endpoint, whose native counter and consequences prove the displayed
statements without any branch-certificate or exactness hypothesis.

**What a reader inspects.** Read the definitions below, the displayed `Encoding` foundation,
and the one additional allowed module, `MultiTape.ResourceBounds`. The latter contributes only
the plain native `ComputableInO` resource convention, explained below, over upstream deterministic
machines. No CNF implementation, complexity-class definition or counting construction is
allowlisted. Lean checks the bridge proofs; `#check_abstract` audits the dependency boundary
of the definitions and theorem statements, not their English interpretation.

## References and credit

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], revised 25 October 2026,
  Sections 3–6, Proposition 6.4, pp. 43–44, and Appendices A–B. Source revision:
  `openai/math@7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
* [R. Impagliazzo and R. Paturi, *On the complexity of k-SAT*][ImpagliazzoPaturi2001]: the
  exponential-time hypotheses and the infimum exponent.

The native port is the joint work recorded in #1226, including Samuel Schlesinger,
Anton Kovsharov, Erik Demaine and the contributing Codex, Claude and Jetski workers. The native
machine and encoding foundations include Christian Reitwiessner's contributions.
Construction provenance is recorded in
`SubexponentialSATBridge`.
-/

namespace ComplexityAbstracts.SubexponentialSATAbstract

/-! ## Formulas and model counting

A literal is a variable or its negation. Clauses are disjunctions of literals and formulas are
conjunctions of clauses; repeated literals and clauses are permitted. A width bound counts literal
occurrences, including repetitions.
-/

/-- A literal: the variable `var`, positive or negated. It is the pair `(var, positive)`. -/
abbrev Literal := ℕ × Bool

/-- The variable of a literal. -/
abbrev Literal.var (l : Literal) : ℕ := l.1

/-- Whether the literal is the variable itself (`true`) or its negation (`false`). -/
abbrev Literal.positive (l : Literal) : Bool := l.2

/-- A clause is a disjunction of literals. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses. -/
abbrev Formula := List Clause

/-- Evaluate a formula: every clause must contain a literal that is true under `σ`, that is,
whose variable's value matches its polarity. -/
def eval (φ : Formula) (σ : ℕ → Bool) : Bool :=
  φ.all fun clause => clause.any fun literal => σ literal.var == literal.positive

/-- A formula is satisfiable when some total Boolean assignment makes it true. -/
def Satisfiable (φ : Formula) : Prop := ∃ σ : ℕ → Bool, eval φ σ = true

/-- Variables in occurrence order, retaining repetitions. -/
def vars (φ : Formula) : List ℕ := φ.flatten.map Literal.var

/-- The number of distinct occurring variables, independent of their numeric labels. -/
def numVars (φ : Formula) : ℕ := (vars φ).toFinset.card

/-- The number of satisfying assignments of `φ`: assignments of its distinct variables, each
variable counted once, that make `φ` true. -/
def modelCount (φ : Formula) : ℕ :=
  (Finset.univ.filter fun σ : (vars φ).toFinset → Bool =>
    eval φ (fun v => if h : v ∈ (vars φ).toFinset then σ ⟨v, h⟩ else false) = true).card

/-- Every clause of `φ` has at most `k` literals. -/
def HasWidth (k : ℕ) (φ : Formula) : Prop := ∀ clause ∈ φ, clause.length ≤ k

/-! ## Representation details

The input is the encoded formula `encCNF φ`. Literal indices are binary; large or non-dense
labels are not silently treated as small. A natural output uses canonical binary digits, with zero
encoded by the empty word. The shared foundation spells out all framing and list conventions.
-/

/-- Encode each literal as a framed binary index followed by its polarity bit; frame the
literals within clauses and the clauses within the formula. This is the native `encCNF`. -/
def encCNF : Formula ↪ List Bool :=
  ComplexityTests.Abstracts.Encoding.encList (ComplexityTests.Abstracts.Encoding.encList
    (ComplexityTests.Abstracts.Encoding.encPair ComplexityTests.Abstracts.Encoding.encNat
      ComplexityTests.Abstracts.Encoding.encBool))

/-! ## Deterministic machine and resource conventions

The upstream model is a deterministic binary multi-tape Turing machine with finitely many
states and a fixed finite number of work tapes. Each transition performs bounded head moves
and symbol operations. The input tape is read-only, and output is write-only. Time counts
transitions until halting; work space counts visited work-tape cells over every run prefix.
No condition is imposed on bitstrings outside the chosen encoding's image.

The native predicate `Turing.MultiTapeTM.ComputableInO f encIn encOut T S` means that there
exists a constant `C` and one such machine computing `f` on every encoded input `x` within
`C * (T x + 1)` steps and `C * (S x + 1)` work cells, with the additional bound
`(encOut (f x)).length ≤ C * (S x + 1)`. Thus output is charged even though its tape is not a
work tape. Time and space are independent budgets; a time bound does not supply polynomial
space. This is the library's existing resource predicate, not a unit-cost arithmetic machine.

For decision problems below, `DecidableInTimeAndSpace` computes the exact Boolean membership
bit and halts on every encoded instance. Its finite machine and all bounds precede the inputs.
-/

/-- A decision problem is decidable in time `O(T x)`, with some independent space bound. -/
def DecidableInTimeO {α : Type} (A : Set α) (enc : α ↪ List Bool) (T : α → ℝ) : Prop :=
  ∃ c : ℕ, ∃ t s : α → ℕ, (∀ x, (t x : ℝ) ≤ c * T x + c) ∧
    Turing.MultiTapeTM.DecidableInTimeAndSpace A enc t s

/-- Exponential time in a parameter, with a polynomial factor in the encoded input length. -/
def DecidableInExpTime {α : Type} (A : Set α) (enc : α ↪ List Bool)
    (μ : α → ℕ) (δ : ℝ) : Prop :=
  ∃ e : ℕ, DecidableInTimeO A enc fun x => 2 ^ (δ * μ x) * ((enc x).length + 1) ^ e

/-! ## The exponential time hypotheses

The decision parameter is the number of distinct occurring variables, not the largest label.
The bridge therefore uses the native dense-relabeling correspondence. Zero infimum exponent alone
does not assert a polynomial-time algorithm.
-/

/-- `k`-SAT consists of satisfiable formulas whose clauses have at most `k` literals. -/
def KSAT (k : ℕ) : Set Formula :=
  {φ | (∀ clause ∈ φ, clause.length ≤ k) ∧ Satisfiable φ}

/-- The infimum of all nonnegative exponential rates admitting a `k`-SAT decider. -/
noncomputable def satExponent (k : ℕ) : ℝ :=
  sInf {δ | 0 ≤ δ ∧ DecidableInExpTime (KSAT k) encCNF numVars δ}

/-- ETH asserts that some positive exponential rate is unattainable for 3SAT. -/
def ETH : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ¬DecidableInExpTime (KSAT 3) encCNF numVars δ

/-- SETH asserts that every improvement below rate one fails for some fixed clause width. -/
def SETH : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ¬DecidableInExpTime (KSAT k) encCNF numVars (1 - ε)

/-! ## Exact counting and the exponential time hypotheses

The primary theorem fixes the counter, constants and native machine for each `k` before every
input. It includes `k = 0, 1`, empty formulas and empty clauses. On formulas with a clause longer
than `k` the output is unspecified; the time and space bounds still hold there.

The scale uses natural logarithms and a shift by sixteen to cover all natural `n`; this changes
only constants in the asymptotic bound. It is the scale of Proposition 6.4, not the smaller
exponent of Theorem 1.1. The proof relabels the variables densely and runs the native
declared-variable counter.
-/

/-- The interpolation-scale exponent, defined at every natural input. -/
noncomputable def interpolationScale (n : ℕ) : ℝ :=
  n * Real.log (Real.log ((n : ℝ) + 16)) ^ 2 / Real.sqrt (Real.log ((n : ℝ) + 16))

/-- For each fixed width `k`, one machine counts the satisfying assignments of every width-`k`
formula in time `2 ^ (A · n (log log n)² / sqrt(log n)) · poly(L)` and space `poly(L)`, where `n`
is the number of variables and `L` the encoding length. -/
theorem exact_count (k : ℕ) :
    ∃ (count : Formula → ℕ) (A e b : ℕ),
      (∀ φ, HasWidth k φ → count φ = modelCount φ) ∧
      Turing.MultiTapeTM.ComputableInO count encCNF ComplexityTests.Abstracts.Encoding.encNat
        (fun φ => ⌈(2 : ℝ) ^ (A * interpolationScale (numVars φ))⌉₊ * ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) :=
  SubexponentialSATBridge.exact_count k

/-- The exponential time hypothesis is false. -/
theorem not_eth : ¬ETH := SubexponentialSATBridge.not_eth

/-- The strong exponential time hypothesis is false. -/
theorem not_seth : ¬SETH := SubexponentialSATBridge.not_seth

/-- Every fixed-width SAT exponent is zero. -/
theorem satExponent_eq_zero : ∀ k, satExponent k = 0 :=
  SubexponentialSATBridge.satExponent_eq_zero

end ComplexityAbstracts.SubexponentialSATAbstract

/--
info: abstract audit passed for `ComplexityAbstracts.SubexponentialSATAbstract`:
25 root declarations, 139 dependencies checked
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityAbstracts.SubexponentialSATAbstract allowing [
  ComplexityAbstracts.Encoding,
  Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds
]
