/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.BPP
public import Complexity.Computability.Complexity.Classes.Promise.Reduction
public import Complexity.Computability.Complexity.Classes.RP
public import Complexity.Computability.Probabilistic.PPT
public import Complexity.Languages.Probabilistic.Notation
import Complexity.Computability.Complexity.Classes.RP.Closure
import Complexity.Computability.Complexity.Classes.SharpP.Combinators
import Complexity.Computability.Complexity.Classes.SharpP.Probability
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Probabilistic.CoinTape
import Complexity.Computability.Probabilistic.PPT.Capture
import Complexity.Computability.Probabilistic.Sampling
import Complexity.Probability.PMF.Uniform

/-!
# Probabilistic classes of promise problems

The probabilistic promise classes `PromiseBPP`, `PromiseRP` and `PromiseCoRP` follow Goldreich's
semantic definitions [Goldreich, Definition 1.2 and Section 6.2][Goldreich2006], requiring bounded
or one-sided error only on instances in the promise. On decision problems embedded via
`PromiseProblem.ofSet`, they agree with `BPP`, `RP` and `coRP` (`ofSet_mem_PromiseBPP`,
`ofSet_mem_PromiseRP`, `ofSet_mem_PromiseCoRP`), and they contain the lifted classes
`promiseClass (BPP enc)`, `promiseClass (RP enc)` and `promiseClass (coRP enc)`.

Each class is equivalent to its uniform strict PPT program characterization
(`mem_PromiseBPP_iff_exists_isPPTOn`, `mem_PromiseRP_iff_exists_isPPTOn`,
`mem_PromiseCoRP_iff_exists_isPPTOn`) via saved-coin replay (`IsPPTOn.exists_seeded_evaluator`,
`IsPPTOn.exists_total_seeded_evaluator`), and is closed under deterministic polynomial-time promise
reductions (`PromiseProblem.PolyTimeReducible.mem_PromiseBPP`,
`PromiseProblem.PolyTimeReducible.mem_PromiseRP`,
`PromiseProblem.PolyTimeReducible.mem_PromiseCoRP`).

## Main definitions

* `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError`,
  `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError`: Goldreich's bounded-error and
  one-sided-error conditions on a promise problem.
* `Cslib.Complexity.PromiseBPP`, `Cslib.Complexity.PromiseRP`, `Cslib.Complexity.PromiseCoRP`:
  the probabilistic classes of promise problems.

## Main results

* `Cslib.Complexity.PromiseProblem.solvesWithBoundedError_ofSet_iff`,
  `Cslib.Complexity.PromiseProblem.solvesWithOneSidedError_ofSet_iff`: on decision problems,
  `SolvesWithBoundedError` and `SolvesWithOneSidedError` agree with `DecidesWithBoundedError` and
  `DecidesWithOneSidedError`.
* `Cslib.Complexity.PromiseProblem.SolvesWithBoundedError.compl`,
  `Cslib.Complexity.PromiseProblem.SolvesWithOneSidedError.exists_certificate`: complement closure
  of bounded-error solvers and witness extraction from one-sided-error solvers.
* `Cslib.Complexity.mem_PromiseBPP_iff`, `Cslib.Complexity.mem_PromiseRP_iff`,
  `Cslib.Complexity.mem_PromiseCoRP_iff`: seeded-verifier characterizations.
* `Cslib.Complexity.ofSet_mem_PromiseBPP`, `Cslib.Complexity.ofSet_mem_PromiseRP`,
  `Cslib.Complexity.ofSet_mem_PromiseCoRP`, `Cslib.Complexity.promiseClass_BPP_subset_PromiseBPP`,
  `Cslib.Complexity.promiseClass_RP_subset_PromiseRP`,
  `Cslib.Complexity.promiseClass_coRP_subset_PromiseCoRP`: agreement with `BPP`, `RP` and `coRP`
  on decision problems and inclusion of `promiseClass`.
* `Cslib.Complexity.compl_mem_PromiseBPP`, `Cslib.Complexity.compl_mem_PromiseRP_iff`,
  `Cslib.Complexity.compl_mem_PromiseCoRP_iff`: complement relations among `PromiseBPP`,
  `PromiseRP` and `PromiseCoRP`.
* `Cslib.Complexity.PromiseP_subset_PromiseRP`, `Cslib.Complexity.PromiseP_subset_PromiseCoRP`,
  `Cslib.Complexity.PromiseP_subset_PromiseBPP`, `Cslib.Complexity.PromiseRP_subset_PromiseNP`,
  `Cslib.Complexity.PromiseRP_subset_PromiseBPP`, `Cslib.Complexity.PromiseCoRP_subset_PromiseBPP`:
  class inclusions among promise classes.
* `Cslib.Complexity.mem_PromiseBPP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseRP_iff_exists_isPPTOn`,
  `Cslib.Complexity.mem_PromiseCoRP_iff_exists_isPPTOn`: characterizations by uniform strict PPT
  programs.
* `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseBPP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseRP`,
  `Cslib.Complexity.PromiseProblem.PolyTimeReducible.mem_PromiseCoRP`: closure of probabilistic
  promise classes under deterministic polynomial-time reductions.

## References

* [O. Goldreich, *On promise problems: a survey*][Goldreich2006]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Probability PromiseProblem

namespace PromiseProblem

variable {α : Type} {enc : α ↪ List Bool} {p : Polynomial ℕ} {V : α × List Bool → Bool}
  {Q : PromiseProblem α} {A : Set α}

/-- `V` solves the promise problem `Q` with bounded error, using random strings whose length is `p`
evaluated at the length of the encoded instance: for every yes-instance at least two thirds of the
random strings are accepted, and for every no-instance at least two thirds are rejected
[Goldreich, Definition 1.2][Goldreich2006]. Nothing is required on instances outside the promise. -/
def SolvesWithBoundedError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  (∀ a ∈ Q.yes, 2 * 2 ^ p.eval (enc a).length ≤
    3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = true).card) ∧
  ∀ a ∈ Q.no, 2 * 2 ^ p.eval (enc a).length ≤
    3 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = false).card

/-- `V` solves the promise problem `Q` with one-sided error, using random strings whose length is
`p` evaluated at the length of the encoded instance: for every yes-instance at least half of the
random strings are accepted, and for every no-instance none is
[Goldreich, Section 6.2][Goldreich2006]. Nothing is required on instances outside the promise. -/
def SolvesWithOneSidedError (enc : α ↪ List Bool) (p : Polynomial ℕ)
    (V : α × List Bool → Bool) (Q : PromiseProblem α) : Prop :=
  (∀ a ∈ Q.yes, 2 ^ p.eval (enc a).length ≤
    2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
      V (a, List.ofFn r) = true).card) ∧
  ∀ a ∈ Q.no, ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = false

/-- On a decision problem, `SolvesWithBoundedError` is `DecidesWithBoundedError`. -/
@[simp]
theorem solvesWithBoundedError_ofSet_iff :
    (ofSet A).SolvesWithBoundedError enc p V ↔ DecidesWithBoundedError enc p V A := by
  simp only [SolvesWithBoundedError, DecidesWithBoundedError, yes_ofSet, no_ofSet,
    Set.mem_compl_iff]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

/-- On a decision problem, `SolvesWithOneSidedError` is `DecidesWithOneSidedError`. -/
@[simp]
theorem solvesWithOneSidedError_ofSet_iff :
    (ofSet A).SolvesWithOneSidedError enc p V ↔ DecidesWithOneSidedError enc p V A := by
  simp only [SolvesWithOneSidedError, DecidesWithOneSidedError, yes_ofSet, no_ofSet,
    Set.mem_compl_iff]
  exact ⟨fun h a => ⟨h.1 a, h.2 a⟩, fun h => ⟨fun a => (h a).1, fun a => (h a).2⟩⟩

/-- Negating the verifier solves the complement promise problem with bounded error. -/
theorem SolvesWithBoundedError.compl (h : Q.SolvesWithBoundedError enc p V) :
    Qᶜ.SolvesWithBoundedError enc p (fun x => !V x) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · simpa using h.2 a ha
  · simpa using h.1 a ha

/-- A one-sided-error solver for a promise problem is a polynomial-time verifier on the promise. -/
theorem SolvesWithOneSidedError.exists_certificate (h : Q.SolvesWithOneSidedError enc p V) :
    (∀ a ∈ Q.yes, ∃ w : List Bool, w.length = p.eval (enc a).length ∧ V (a, w) = true) ∧
      ∀ a ∈ Q.no, ∀ w : List Bool, w.length = p.eval (enc a).length → V (a, w) = false := by
  refine ⟨fun a ha => ?_, fun a ha w hw => ?_⟩
  · have hpos := Nat.one_le_two_pow (n := p.eval (enc a).length)
    obtain ⟨r, hr⟩ : (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
        V (a, List.ofFn r) = true).Nonempty := by
      rw [← Finset.card_pos]
      have := h.1 a ha
      omega
    exact ⟨List.ofFn r, List.length_ofFn, (Finset.mem_filter.1 hr).2⟩
  · have hno := h.2 a ha fun i => w[i.val]'(by omega)
    rwa [show (List.ofFn fun i : Fin (p.eval (enc a).length) => w[i.val]'(by omega)) = w from
      List.ext_getElem (by simp [hw]) fun i _ _ => by simp] at hno

end PromiseProblem

section PromiseProbabilistic

variable {α : Type} {enc : α ↪ List Bool} {Q : PromiseProblem α} {A : Set α}

/-- The promise problems solved with bounded error by polynomial-time algorithms reading
polynomially long random strings, with respect to the encoding `enc` of instances
[Goldreich, Definition 1.2][Goldreich2006]. -/
def PromiseBPP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithBoundedError enc p V}

/-- The promise problems solved with one-sided error (no false positives on no-instances) by
polynomial-time algorithms reading polynomially long random strings
[Goldreich, Section 6.2][Goldreich2006]. -/
def PromiseRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
    ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithOneSidedError enc p V}

/-- The promise problems solved with one-sided error (no false negatives on yes-instances) by
polynomial-time algorithms reading polynomially long random strings: those whose complements are
in `PromiseRP` [Goldreich, Section 6.2][Goldreich2006]. -/
def PromiseCoRP (enc : α ↪ List Bool) : Set (PromiseProblem α) :=
  {Q | Qᶜ ∈ PromiseRP enc}

/-- Membership in `PromiseBPP` unfolded to a polynomial coin bound and a polynomial-time
bounded-error solver. -/
theorem mem_PromiseBPP_iff : Q ∈ PromiseBPP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithBoundedError enc p V :=
  Iff.rfl

/-- Membership in `PromiseRP` unfolded to a polynomial coin bound and a polynomial-time
one-sided-error solver. -/
theorem mem_PromiseRP_iff : Q ∈ PromiseRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      Q.SolvesWithOneSidedError enc p V :=
  Iff.rfl

/-- A promise problem is in `PromiseCoRP` when a polynomial-time verifier accepts every random
string on every yes-instance and rejects at least half on every no-instance. -/
theorem mem_PromiseCoRP_iff : Q ∈ PromiseCoRP enc ↔
    ∃ (p : Polynomial ℕ) (V : α × List Bool → Bool),
      ComputableInPolyTime V (encPair enc encBits) encBool ∧
      (∀ a ∈ Q.yes, ∀ r : Fin (p.eval (enc a).length) → Bool, V (a, List.ofFn r) = true) ∧
      ∀ a ∈ Q.no, 2 ^ p.eval (enc a).length ≤
        2 * (Finset.univ.filter fun r : Fin (p.eval (enc a).length) → Bool =>
          V (a, List.ofFn r) = false).card := by
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨p, fun x => !V x, ComputableInPolyTime.bool_not.comp hV,
      fun a ha r => by simp [hno a ha r], fun a ha => by simpa using hyes a ha⟩
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨p, fun x => !V x, ComputableInPolyTime.bool_not.comp hV,
      fun a ha => by simpa using hno a ha, fun a ha r => by simp [hyes a ha r]⟩

/-- A total language embedded as a promise problem belongs to `PromiseBPP` if and only if
it belongs to `BPP`. -/
@[simp]
theorem ofSet_mem_PromiseBPP : ofSet A ∈ PromiseBPP enc ↔ A ∈ BPP enc := by
  simp only [PromiseBPP, BPP, Set.mem_ofPred_eq, solvesWithBoundedError_ofSet_iff]

/-- A total language embedded as a promise problem belongs to `PromiseRP` if and only if
it belongs to `RP`. -/
@[simp]
theorem ofSet_mem_PromiseRP : ofSet A ∈ PromiseRP enc ↔ A ∈ RP enc := by
  simp only [PromiseRP, RP, Set.mem_ofPred_eq, solvesWithOneSidedError_ofSet_iff]

/-- A total language embedded as a promise problem belongs to `PromiseCoRP` if and only if
it belongs to `coRP`. -/
@[simp]
theorem ofSet_mem_PromiseCoRP : ofSet A ∈ PromiseCoRP enc ↔ A ∈ coRP enc := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, ← ofSet_compl, ofSet_mem_PromiseRP, mem_coRP]

/-- Every promise problem separated by a language in `BPP` is in `PromiseBPP`. -/
theorem promiseClass_BPP_subset_PromiseBPP : promiseClass (BPP enc) ⊆ PromiseBPP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a ha => (hB a).1 (hyes ha),
    fun a ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩

/-- Every promise problem separated by a language in `RP` is in `PromiseRP`. -/
theorem promiseClass_RP_subset_PromiseRP : promiseClass (RP enc) ⊆ PromiseRP enc := by
  rintro Q ⟨B, ⟨p, V, hV, hB⟩, hyes, hno⟩
  exact ⟨p, V, hV, fun a ha => (hB a).1 (hyes ha),
    fun a ha => (hB a).2 (Set.disjoint_right.1 hno ha)⟩

/-- Every promise problem separated by a language in `coRP` is in `PromiseCoRP`. -/
theorem promiseClass_coRP_subset_PromiseCoRP : promiseClass (coRP enc) ⊆ PromiseCoRP enc := by
  rintro Q ⟨B, hB, hyes, hno⟩
  exact promiseClass_RP_subset_PromiseRP ⟨Bᶜ, hB,
    Set.subset_compl_iff_disjoint_left.2 hno, Set.disjoint_compl_left_iff_subset.2 hyes⟩

/-- `PromiseBPP` is closed under complement. -/
theorem compl_mem_PromiseBPP (hQ : Q ∈ PromiseBPP enc) : Qᶜ ∈ PromiseBPP enc :=
  let ⟨p, V, hV, h⟩ := hQ
  ⟨p, fun x => !V x, ComputableInPolyTime.bool_not.comp hV, h.compl⟩

/-- A promise problem's complement is in `PromiseRP` exactly when the problem is in
`PromiseCoRP`. -/
theorem compl_mem_PromiseRP_iff : Qᶜ ∈ PromiseRP enc ↔ Q ∈ PromiseCoRP enc :=
  Iff.rfl

/-- A promise problem's complement is in `PromiseCoRP` exactly when the problem is in
`PromiseRP`. -/
theorem compl_mem_PromiseCoRP_iff : Qᶜ ∈ PromiseCoRP enc ↔ Q ∈ PromiseRP enc := by
  rw [← compl_mem_PromiseRP_iff, compl_compl]

/-- Every promise problem in `PromiseP` is in `PromiseRP`. -/
theorem PromiseP_subset_PromiseRP : PromiseP enc ⊆ PromiseRP enc :=
  (promiseClass_mono P_subset_RP).trans promiseClass_RP_subset_PromiseRP

/-- Every promise problem in `PromiseP` is in `PromiseCoRP`. -/
theorem PromiseP_subset_PromiseCoRP : PromiseP enc ⊆ PromiseCoRP enc :=
  (promiseClass_mono P_subset_coRP).trans promiseClass_coRP_subset_PromiseCoRP

/-- Every promise problem in `PromiseP` is in `PromiseBPP`. -/
theorem PromiseP_subset_PromiseBPP : PromiseP enc ⊆ PromiseBPP enc :=
  (promiseClass_mono P_subset_BPP).trans promiseClass_BPP_subset_PromiseBPP

/-- Every promise problem in `PromiseRP` is in `PromiseNP`. -/
theorem PromiseRP_subset_PromiseNP : PromiseRP enc ⊆ PromiseNP enc := by
  rintro Q ⟨p, V, hV, h⟩
  exact mem_PromiseNP_iff.2 ⟨p, V, hV, h.exists_certificate⟩

/-- **Probabilistic-program characterization of `PromiseBPP`**: a promise problem is in
`PromiseBPP` exactly when a uniform strict PPT Boolean program accepts every yes-instance with
probability at least `2 / 3` and rejects every no-instance with probability at least `2 / 3`. -/
theorem mem_PromiseBPP_iff_exists_isPPTOn : Q ∈ PromiseBPP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 2 / 3 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, 2 / 3 ≤ Pr[Bool.not <$> M a] := by
  rw [mem_PromiseBPP_iff]
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)) hV,
      fun a ha => ?_, fun a ha => ?_⟩
    · simp only [ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_acceptCount_toReal, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast hyes a ha
      linarith
    · simp only [Functor.map_map, ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_acceptCount_toReal (V := fun x => !V x), le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤
          3 * (acceptCount (fun x => !V x) a (p.eval (enc a).length) : ℝ) := by
        simpa only [acceptCount, Bool.not_eq_true'] using
          (by exact_mod_cast hno a ha : (2 : ℝ) * 2 ^ p.eval (enc a).length ≤ _)
      linarith
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hlaw⟩ := hM.exists_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, .of_tidy hevalM,
      fun a ha => ?_, fun a ha => ?_⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h3
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hno a ha
      have hmap : ProbComp.eval (Bool.not <$> M a) =
          (BitString.uniformList (c * ((enc a).length + 1) ^ d)).map (fun w => !evalM a w) := by
        rw [ProbComp.eval_map, hlaw a, PMF.map_comp]
        rfl
      rw [hmap, uniformList_acceptCount_toReal (V := fun x => !evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h3 : (2 : ℝ) * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * (acceptCount (fun x => !evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      simpa only [acceptCount, Bool.not_eq_true'] using (by exact_mod_cast h3 :
        2 * 2 ^ (c * ((enc a).length + 1) ^ d) ≤
          3 * acceptCount (fun x => !evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d))

/-- **Probabilistic-program characterization of `PromiseRP`**: a promise problem is in `PromiseRP`
exactly when a uniform strict PPT Boolean program accepts every yes-instance with probability at
least `1 / 2` and never accepts a no-instance. -/
theorem mem_PromiseRP_iff_exists_isPPTOn : Q ∈ PromiseRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, 1 / 2 ≤ Pr[M a]) ∧
      ∀ a ∈ Q.no, true ∉ (ProbComp.eval (M a)).support := by
  rw [mem_PromiseRP_iff]
  constructor
  · rintro ⟨p, V, hV, hyes, hno⟩
    refine ⟨fun a => (fun w => V (a, w)) <$> BitString.sampleList (p.eval (enc a).length),
      IsPPTOn.of_seeded ((ComputableInPolyTime.unary_eval p).comp
        (ComputableInPolyTime.encoding_length enc)) hV,
      fun a ha => ?_, fun a ha hmem => ?_⟩
    · simp only [ProbComp.eval_map, BitString.eval_sampleList]
      rw [uniformList_acceptCount_toReal, le_div_iff₀ (by positivity)]
      have h : (2 : ℝ) ^ p.eval (enc a).length ≤
          2 * (acceptCount V a (p.eval (enc a).length) : ℝ) := by
        exact_mod_cast hyes a ha
      linarith
    · simp only [ProbComp.eval_map, BitString.eval_sampleList,
        PMF.mem_support_map_iff, BitString.mem_support_uniformList_iff] at hmem
      obtain ⟨w, hw, hVw⟩ := hmem
      have := (SolvesWithOneSidedError.exists_certificate ⟨hyes, hno⟩).2 a ha w hw
      rw [this] at hVw
      exact Bool.noConfusion hVw
  · rintro ⟨M, hM, hyes, hno⟩
    obtain ⟨c, d, evalM, hevalM, hsupp, hlaw⟩ := hM.exists_total_seeded_evaluator
    refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun x => evalM x.1 x.2, .of_tidy hevalM,
      fun a ha => ?_, fun a ha r => ?_⟩
    · have hp : (Polynomial.C c * (Polynomial.X + 1) ^ d).eval (enc a).length =
          c * ((enc a).length + 1) ^ d := by simp
      rw [hp]
      have hprob := hyes a ha
      rw [hlaw a _ le_rfl, uniformList_acceptCount_toReal (V := fun x => evalM x.1 x.2),
        le_div_iff₀ (by positivity)] at hprob
      have h2 : (2 : ℝ) ^ (c * ((enc a).length + 1) ^ d) ≤
          2 * (acceptCount (fun x => evalM x.1 x.2) a (c * ((enc a).length + 1) ^ d) : ℝ) := by
        linarith
      exact_mod_cast h2
    · rw [← Bool.not_eq_true]
      intro htrue
      exact hno a ha (htrue ▸ hsupp a (List.ofFn r))

/-- **Probabilistic-program characterization of `PromiseCoRP`**: a promise problem is in
`PromiseCoRP` exactly when a uniform strict PPT Boolean program never rejects a yes-instance and
rejects every no-instance with probability at least `1 / 2`. -/
theorem mem_PromiseCoRP_iff_exists_isPPTOn : Q ∈ PromiseCoRP enc ↔
    ∃ M : α → ProbComp Bool, IsPPTOn enc encBool M ∧
      (∀ a ∈ Q.yes, false ∉ (ProbComp.eval (M a)).support) ∧
      ∀ a ∈ Q.no, 1 / 2 ≤ Pr[Bool.not <$> M a] := by
  rw [PromiseCoRP, Set.mem_ofPred_eq, mem_PromiseRP_iff_exists_isPPTOn]
  constructor
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a,
      hM.map_with (ComputableInPolyTime.bool_not.comp (.snd enc encBool)),
      fun a ha hmem => ?_, fun a ha => ?_⟩
    · simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
        Bool.not_eq_false'] at hmem
      obtain ⟨b, hb, rfl⟩ := hmem
      exact hno a ha hb
    · have h : Bool.not <$> (Bool.not <$> M a) = M a := by simp
      rw [h]
      exact hyes a ha
  · rintro ⟨M, hM, hyes, hno⟩
    refine ⟨fun a => Bool.not <$> M a,
      hM.map_with (ComputableInPolyTime.bool_not.comp (.snd enc encBool)),
      fun a ha => hno a ha, fun a ha hmem => ?_⟩
    simp only [ProbComp.eval_map, PMF.mem_support_map_iff,
      Bool.not_eq_true'] at hmem
    obtain ⟨b, hb, rfl⟩ := hmem
    exact hyes a ha hb

/-- Every promise problem in `PromiseRP` is in `PromiseBPP`. -/
theorem PromiseRP_subset_PromiseBPP : PromiseRP enc ⊆ PromiseBPP enc := by
  intro Q ⟨p, V, hV, hyes, hno⟩
  have hk : ComputableInPolyTime (fun a => p.eval (enc a).length) enc encUnary :=
    (ComputableInPolyTime.unary_eval p).comp
      (ComputableInPolyTime.encoding_length enc)
  refine ⟨p + p, orVerifier (fun a => p.eval (enc a).length) V V,
    computableInPolyTime_orVerifier hk hV hV, fun a ha => ?_, fun a ha => ?_⟩
  · change 2 * 2 ^ (p + p).eval (enc a).length ≤
      3 * acceptCount (orVerifier (fun a => p.eval (enc a).length) V V) a
        ((p + p).eval (enc a).length)
    rw [Polynomial.eval_add]
    generalize hk₀ : p.eval (enc a).length = k
    have hc := acceptCount_orVerifier (fun a => p.eval (enc a).length) V V a k
    simp only [hk₀] at hc ⊢
    have n₁ := acceptCount_add_acceptCount_not V a k
    have hhalf : 2 ^ k ≤ 2 * acceptCount V a k := hk₀ ▸ hyes a ha
    have hrej : 2 * acceptCount (fun x => !V x) a k ≤ 2 ^ k := by omega
    have hprod : 4 * (acceptCount (fun x => !V x) a k * acceptCount (fun x => !V x) a k) ≤
        2 ^ (k + k) := by
      rw [pow_add]
      nlinarith [Nat.mul_le_mul hrej hrej]
    omega
  · rw [Polynomial.eval_add]
    have hall (r : Fin (p.eval (enc a).length + p.eval (enc a).length) → Bool) :
        orVerifier (fun a => p.eval (enc a).length) V V (a, List.ofFn r) = false := by
      simp only [orVerifier, Bool.or_eq_false_iff]
      have hcert := (SolvesWithOneSidedError.exists_certificate ⟨hyes, hno⟩).2 a ha
      exact ⟨hcert _ (by simp), hcert _ (by simp)⟩
    rw [Finset.filter_true_of_mem fun r _ => hall r]
    simp only [Finset.card_univ, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
    omega

/-- Every promise problem in `PromiseCoRP` is in `PromiseBPP`. -/
theorem PromiseCoRP_subset_PromiseBPP : PromiseCoRP enc ⊆ PromiseBPP enc := fun Q hQ => by
  simpa using compl_mem_PromiseBPP (PromiseRP_subset_PromiseBPP hQ)

end PromiseProbabilistic

namespace PromiseProblem

variable {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {X : PromiseProblem α} {Y : PromiseProblem β}

/-- **`PromiseBPP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseBPP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseBPP encB) : X ∈ PromiseBPP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseBPP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseBPP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseRP encB) : X ∈ PromiseRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

/-- **`PromiseCoRP` is closed under polynomial-time reductions.** -/
theorem PolyTimeReducible.mem_PromiseCoRP (h : PolyTimeReducible encA encB X Y)
    (hY : Y ∈ PromiseCoRP encB) : X ∈ PromiseCoRP encA := by
  obtain ⟨f, hf, hfyes, hfno⟩ := h
  obtain ⟨M, hM, hyes, hno⟩ := mem_PromiseCoRP_iff_exists_isPPTOn.mp hY
  exact mem_PromiseCoRP_iff_exists_isPPTOn.mpr
    ⟨fun a => M (f a), hM.preprocess hf, fun a ha => hyes (f a) (hfyes ha),
      fun a ha => hno (f a) (hfno ha)⟩

end PromiseProblem

end Cslib.Complexity
