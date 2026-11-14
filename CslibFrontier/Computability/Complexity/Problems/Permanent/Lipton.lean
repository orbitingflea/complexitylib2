/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.SelfCorrection
public import CslibFrontier.Foundations.Data.Matrix.Permanent.Line
public import CslibFrontier.Languages.Probabilistic.Oracle.Vector
public import CslibFrontier.Languages.Probabilistic.Plurality
public import CslibFrontier.Probability.Uniform.AffineLine
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.ToReal

/-!
# Lipton's permanent random self-reduction in the `ProbOracleComp` query-complexity model

In the `Cslib.ProbOracleComp` query-complexity model (where finite-field arithmetic and uniform
matrix sampling are performed in `F` rather than charged as bit-level Turing-machine steps), given
an oracle `O : Matrix (Fin n) (Fin n) F → F` over a finite field `F` that agrees with the matrix
permanent on most matrices, Lipton's random self-reduction (R. J. Lipton, *New directions in
testing*, 1991; after [Arora and Barak][AroraBarak09], Theorem 8.30) recovers `A.permanent` in the
worst case for every matrix `A : Matrix (Fin n) (Fin n) F`:

1. **Single-trial interpolation (`liptonPermanentTrial`).** Choose `n + 1` distinct nonzero nodes
   `ν : Fin (n + 1) ↪ F` (`Cslib.Code.nonzeroNodes`, which exist whenever `n + 2 ≤ Fintype.card F`,
   and in particular under `3 * n < Fintype.card F` for `1 ≤ n` via
   `add_two_le_card_of_three_mul_lt`). Sample `R : Matrix (Fin n) (Fin n) F` uniformly at random,
   query `O (A + ν i • R)` at each `i : Fin (n + 1)`, and combine the replies with the Lagrange
   weights `Cslib.Code.lagrangeWeight ν i` at `0`.
   - Since `t ↦ (A + t • R).permanent` has degree at most `n`
     (`Matrix.exists_natDegree_le_eval_eq_permanent_add_smul`), Lagrange interpolation recovers
     `A.permanent` whenever all `n + 1` queried points avoid the oracle's error set
     (`lagrangeDecode_permanent`).
   - Because `ν i ≠ 0`, each query `A + ν i • R` is individually uniform over
     `Matrix (Fin n) (Fin n) F` (`Cslib.Probability.PMF.map_add_smul_uniformOfFintype`,
     `Cslib.ProbComp.eval_map_add_smul_uniform`).
   - By the union bound over the `n + 1` queries (`card_lagrangeDecode_permanent_ne_le`), the
     single-trial algorithm makes `n + 1` oracle queries (`isQueryBounded_liptonPermanentTrial`,
     `length_transcript_liptonPermanentTrial`) and outputs `A.permanent` with probability at least
     `1 - (n + 1) / (3 * n)` whenever `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`
     (`liptonPermanentTrial_prob_ge`, `liptonPermanentTrial_prob_toReal_ge`,
     `liptonPermanentTrial_prob_ge_of_three_mul_lt`,
     `liptonPermanentTrial_prob_toReal_ge_of_three_mul_lt`).

2. **Plurality amplification (`liptonPermanentPlurality`).** Repeating `liptonPermanentTrial ν A`
   for `k` independent trials and taking the plurality (`Cslib.ProbComp.plurality 0`) makes
   `k * (n + 1)` queries (`isQueryBounded_liptonPermanentPlurality`,
   `length_transcript_liptonPermanentPlurality`) and drives the failure probability down to
   `exp (-2 * k * γ²) ≤ 2^{-(2 * γ² * k)}` whenever a single trial succeeds with margin `γ` above
   `1 / 2` (`liptonPermanentPlurality_prob_toReal_ge_of_margin`).
   - Under the draft's `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)` hypothesis, the union-bound
     single-trial failure rate `(n + 1) / (3 * n)` is `2 / 3` at `n = 1`, `1 / 2` at `n = 2`, and
     at most `4 / 9 = 1 / 2 - 1 / 18` for `3 ≤ n`, giving success probability at least
     `1 - 2^{-k / 162}` (`liptonPermanentPlurality_prob_toReal_ge`,
     `liptonPermanentPlurality_prob_toReal_ge_of_three_mul_lt`).
   - Under `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (4 * n)` for `2 ≤ n`, the margin is `γ = 1 / 8`,
     giving `1 - 2^{-k / 32}` (`liptonPermanentPlurality_prob_toReal_ge_of_four_mul`); under
     `#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * (n + 1))` for all `n`, the margin is `γ = 1 / 6`,
     giving `1 - 2^{-k / 18}` (`liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ`).

## Main definitions

* `Cslib.Complexity.PermanentOracleSpec`: query interface `Matrix (Fin n) (Fin n) F → F`.
* `Cslib.Complexity.liptonPermanentTrial`: single-trial random self-reduction in `ProbOracleComp`.
* `Cslib.Complexity.liptonPermanentPlurality`: `k`-trial plurality-amplified random self-reduction.

## Main results

* `Cslib.Complexity.lagrangeDecode_permanent`,
  `Cslib.Complexity.card_lagrangeDecode_permanent_ne_le`: exact line interpolation of the permanent
  and the `(n + 1) * #{M | O M ≠ M.permanent}` direction-error bound.
* `Cslib.Complexity.run_liptonPermanentTrial`, `Cslib.Complexity.eval_run_liptonPermanentTrial`,
  `Cslib.Complexity.isQueryBounded_liptonPermanentTrial`,
  `Cslib.Complexity.length_transcript_liptonPermanentTrial`: execution semantics and `n + 1` query
  bounds for a single trial.
* `Cslib.Complexity.toOuterMeasure_run_liptonPermanentTrial_ne_le`,
  `Cslib.Complexity.one_sub_le_eval_run_liptonPermanentTrial`,
  `Cslib.Complexity.liptonPermanentTrial_prob_ge`,
  `Cslib.Complexity.liptonPermanentTrial_prob_toReal_ge`,
  `Cslib.Complexity.liptonPermanentTrial_prob_ge_of_three_mul_lt`,
  `Cslib.Complexity.liptonPermanentTrial_prob_toReal_ge_of_three_mul_lt`: single-trial failure and
  success probability bounds in the `ProbOracleComp` query-complexity model (after Arora–Barak
  Theorem 8.30).
* `Cslib.Complexity.run_liptonPermanentPlurality`,
  `Cslib.Complexity.isQueryBounded_liptonPermanentPlurality`,
  `Cslib.Complexity.length_transcript_liptonPermanentPlurality`: execution semantics and
  `k * (n + 1)` query bounds for `k` independent trials.
* `Cslib.Complexity.liptonPermanentPlurality_prob_toReal_ge_of_margin`,
  `Cslib.Complexity.liptonPermanentPlurality_prob_toReal_ge`,
  `Cslib.Complexity.liptonPermanentPlurality_prob_ge`,
  `Cslib.Complexity.liptonPermanentPlurality_prob_toReal_ge_of_three_mul_lt`,
  `Cslib.Complexity.liptonPermanentPlurality_prob_toReal_ge_of_four_mul`,
  `Cslib.Complexity.liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ`: plurality
  amplification bounds.

## Model notes

* **Probabilistic oracle model:** algorithms are expressed in the native `Cslib.ProbOracleComp`
  monad over the typed query interface `PermanentOracleSpec n F`. This is a query-complexity
  milestone: finite-field arithmetic and matrix addition/scaling are performed in `F` rather than
  charged as bit-level Turing machine steps.
* **Precision choice for high probability:** "with high probability" in Arora–Barak Theorem 8.30 is
  made precise by the `k`-trial plurality wrapper `liptonPermanentPlurality k ν A` achieving
  success probability `≥ 1 - 2^{-Ω(k)}` with explicit constants.

## References

* R. J. Lipton, *New directions in testing*, DIMACS Series in Discrete Mathematics and Theoretical
  Computer Science 2 (1991), 191–202.
* [S. Arora and B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09],
  Theorem 8.30 (2007 draft, printed p. 168 / PDF p. 184)
-/

public section

namespace Cslib.Complexity

open Finset Polynomial Probability ProbComp ProbOracleComp
open scoped ENNReal

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {n : ℕ}

/-! ### Algebraic self-correction of the permanent along an affine line -/

omit [Field F] [DecidableEq F] in
private theorem card_matrix_fin :
    Fintype.card (Matrix (Fin n) (Fin n) F) = Fintype.card F ^ (n * n) := by
  change Fintype.card (Fin n → Fin n → F) = _
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul]

omit [Fintype F] [DecidableEq F] in
/-- **Lagrange interpolation along any line recovers the permanent.** For any `n + 1` distinct
evaluation nodes `ν : Fin (n + 1) ↪ F` and matrices `A, R : Matrix (Fin n) (Fin n) F`,
interpolating `(A + ν i • R).permanent` at `0` yields `A.permanent`. -/
theorem lagrangeDecode_permanent (ν : Fin (n + 1) ↪ F) (A R : Matrix (Fin n) (Fin n) F) :
    Code.lagrangeDecode ν Matrix.permanent A R = A.permanent :=
  Code.lagrangeDecode_eq_of_exists_natDegree_le ν
    (by simpa using Matrix.exists_natDegree_le_eval_eq_permanent_add_smul A R)

/-- **Error count for Lipton's line interpolation.** For any `n + 1` distinct nonzero nodes
`ν : Fin (n + 1) ↪ F` and oracle `O : Matrix (Fin n) (Fin n) F → F`, at most
`(n + 1) * #{M | O M ≠ M.permanent}` directions `R` make `Code.lagrangeDecode ν O A R` differ from
`A.permanent`. -/
theorem card_lagrangeDecode_permanent_ne_le (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    #{R | Code.lagrangeDecode ν O A R ≠ A.permanent} ≤
      (n + 1) * #{M | O M ≠ M.permanent} :=
  Code.card_lagrangeDecode_ne_le_of_forall_eq ν hν (lagrangeDecode_permanent ν A) O

omit [Field F] [DecidableEq F] in
/-- The draft's field-size condition `3 * n < Fintype.card F` (for `1 ≤ n`) implies
`n + 2 ≤ Fintype.card F`. -/
theorem add_two_le_card_of_three_mul_lt (hn : 1 ≤ n) (hcard : 3 * n < Fintype.card F) :
    n + 2 ≤ Fintype.card F := by
  omega

/-! ### Native `ProbOracleComp` single-trial algorithm -/

/-- Query interface for an oracle computing a function `Matrix (Fin n) (Fin n) F → F`. -/
abbrev PermanentOracleSpec (n : ℕ) (F : Type) : Matrix (Fin n) (Fin n) F → Type :=
  fun _ => F

/-- **Lipton's single-trial random self-reduction for the permanent in the `ProbOracleComp`
query-complexity model** (after [Arora and Barak][AroraBarak09], Theorem 8.30).
Draws a uniform random matrix `R : Matrix (Fin n) (Fin n) F`, queries the oracle at the `n + 1`
points `A + ν i • R` along the random line through `A`, and returns the Lagrange interpolation at
`0`.

This is a query-complexity milestone in `ProbOracleComp`: field arithmetic and matrix
addition/scaling are performed in `F` rather than charged on a bit-level Turing tape. -/
noncomputable def liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    ProbOracleComp (PermanentOracleSpec n F) F := do
  let R ← ProbOracleComp.sample (ProbComp.uniform (Matrix (Fin n) (Fin n) F))
  let y ← OracleComp.pi (fun i : Fin (n + 1) => ProbOracleComp.query (A + ν i • R))
  return ∑ i : Fin (n + 1), Code.lagrangeWeight ν i * y i

omit [DecidableEq F] in
/-- Against a deterministic oracle `O`, running `liptonPermanentTrial ν A` samples a uniform
direction `R` and computes `Code.lagrangeDecode ν O A R`. -/
@[simp]
theorem run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    (O : Matrix (Fin n) (Fin n) F → F) :
    (liptonPermanentTrial ν A).run (fun M => pure (O M)) =
      Code.lagrangeDecode ν O A <$> ProbComp.uniform (Matrix (Fin n) (Fin n) F) := by
  simp only [liptonPermanentTrial, bind_pure_comp, ProbOracleComp.run_bind,
    ProbOracleComp.run_sample, ProbOracleComp.run_map, run_pi_query, map_pure]
  rfl

omit [DecidableEq F] in
/-- Evaluating `liptonPermanentTrial ν A` against a deterministic oracle `O` pushes the uniform
distribution on `Matrix (Fin n) (Fin n) F` forward along `Code.lagrangeDecode ν O A`. -/
theorem eval_run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    (O : Matrix (Fin n) (Fin n) F → F) :
    ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) =
      (PMF.uniformOfFintype (Matrix (Fin n) (Fin n) F)).map (Code.lagrangeDecode ν O A) := by
  rw [run_liptonPermanentTrial, ProbComp.eval_map, ProbComp.eval_uniform]

omit [DecidableEq F] in
/-- `liptonPermanentTrial ν A` makes at most `n + 1` oracle queries on every execution path. -/
theorem isQueryBounded_liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    (liptonPermanentTrial ν A).IsQueryBounded (n + 1) := by
  unfold liptonPermanentTrial
  refine OracleComp.IsCostBounded.mono (n := 0 + (n + 1)) ?_ (by omega)
  refine (ProbOracleComp.IsQueryBounded.sample _).bind fun R => ?_
  simp only [bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (isQueryBounded_pi_query (fun i : Fin (n + 1) => A + ν i • R))

omit [DecidableEq F] in
/-- **Exact query count of `liptonPermanentTrial`.** Every supported stateful execution of
`liptonPermanentTrial ν A` makes exactly `n + 1` external oracle queries. -/
theorem length_transcript_liptonPermanentTrial {State : Type}
    (oracle : (M : Matrix (Fin n) (Fin n) F) → StateT State PMF F)
    (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    {s s' : State} {result : F} {transcript : OracleComp.Transcript (PermanentOracleSpec n F)}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (liptonPermanentTrial ν A) (s, [])).support) :
    transcript.length = n + 1 := by
  simp only [liptonPermanentTrial, bind_pure_comp, ProbOracleComp.runWith_sample_bind,
    ProbOracleComp.runWith_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
  obtain ⟨R, -, ⟨y, s₂, tr⟩, hy, heq⟩ := hmem
  simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
  rcases heq with ⟨-, rfl, rfl⟩
  exact length_transcript_pi_query oracle (fun i : Fin (n + 1) => A + ν i • R) hy

/-- **Single-trial failure probability bound.** Against a deterministic oracle `O`, the probability
that `liptonPermanentTrial ν A` outputs a value different from `A.permanent` is at most
`((n + 1) * #{M | O M ≠ M.permanent}) / |F|^{n²}`. -/
theorem toOuterMeasure_run_liptonPermanentTrial_ne_le (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))).toOuterMeasure
        {y | y ≠ A.permanent} ≤
      (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
        (Fintype.card F ^ (n * n) : ℕ) := by
  classical
  rw [eval_run_liptonPermanentTrial, PMF.toOuterMeasure_map_apply,
    Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype, card_matrix_fin, ← div_eq_mul_inv]
  refine ENNReal.div_le_div_right ?_ _
  rw [Set.preimage_ofPred_eq]
  exact_mod_cast card_lagrangeDecode_permanent_ne_le ν hν O A

/-- **Single-trial success probability bound in terms of the oracle's error count.** -/
theorem one_sub_le_eval_run_liptonPermanentTrial (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    1 - (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
        (Fintype.card F ^ (n * n) : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) A.permanent := by
  set p := ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_add_compl_ennreal p ({A.permanent} : Set F)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({A.permanent} : Set F)ᶜ = {y | y ≠ A.permanent} := rfl
  rw [hcompl_set] at hcompl
  have hle := toOuterMeasure_run_liptonPermanentTrial_ne_le ν hν O A
  have hne_top := Cslib.Probability.PMF.toOuterMeasure_ne_top p {y | y ≠ A.permanent}
  calc 1 - (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) / (Fintype.card F ^ (n * n) : ℕ)
      ≤ 1 - p.toOuterMeasure {y | y ≠ A.permanent} := tsub_le_tsub_left hle 1
    _ = p A.permanent := by rw [← hcompl, ENNReal.add_sub_cancel_right hne_top]

/-- **Single-trial query-complexity bound (after Arora–Barak Theorem 8.30):** in the
`ProbOracleComp` query-complexity model, if `O` errs on at most `|F|^{n²} / (3 * n)` matrices and
`ν : Fin (n + 1) ↪ F` are `n + 1` distinct nonzero nodes, then `liptonPermanentTrial ν A` outputs
`A.permanent` with probability at least `1 - (n + 1) / (3 * n)` for every `A`. -/
theorem liptonPermanentTrial_prob_ge (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0)
    (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ≥0∞) / (3 * n : ℕ) ≤
      ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M))) A.permanent := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · refine (tsub_le_tsub_left ?_ 1).trans (one_sub_le_eval_run_liptonPermanentTrial ν hν O A)
    have hmul : #{M | O M ≠ M.permanent} * (3 * n) ≤ Fintype.card F ^ (n * n) :=
      Nat.mul_le_of_le_div _ _ _ hO
    have h3n0 : ((3 * n : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
    have h3ntop : ((3 * n : ℕ) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    refine ENNReal.div_le_of_le_mul ?_
    calc (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞)
        = (n + 1 : ℝ≥0∞) * (#{M | O M ≠ M.permanent} : ℕ) *
            ((3 * n : ℕ) * ((3 * n : ℕ) : ℝ≥0∞)⁻¹) := by
          rw [ENNReal.mul_inv_cancel h3n0 h3ntop, mul_one]; push_cast; ring
      _ = (n + 1 : ℝ≥0∞) / (3 * n : ℕ) *
            ((#{M | O M ≠ M.permanent} * (3 * n) : ℕ) : ℝ≥0∞) := by
          rw [div_eq_mul_inv]; push_cast; ring
      _ ≤ (n + 1 : ℝ≥0∞) / (3 * n : ℕ) * (Fintype.card F ^ (n * n) : ℕ) := by
          gcongr

/-- Real-valued single-trial failure probability bound in terms of the oracle's error count. -/
theorem toOuterMeasure_run_liptonPermanentTrial_ne_toReal_le (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    ((ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))).toOuterMeasure
        {y | y ≠ A.permanent}).toReal ≤
      ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) := by
  have hle := toOuterMeasure_run_liptonPermanentTrial_ne_le ν hν O A
  have htop : (((n + 1) * #{M | O M ≠ M.permanent} : ℕ) : ℝ≥0∞) /
      (Fintype.card F ^ (n * n) : ℕ) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
  have hreal := ENNReal.toReal_mono htop hle
  rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast] at hreal
  exact_mod_cast hreal

/-- Real-valued single-trial success probability bound in terms of the oracle's error count. -/
theorem one_sub_le_eval_run_liptonPermanentTrial_toReal (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) (A : Matrix (Fin n) (Fin n) F) :
    1 - ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  set p := ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
  have hcompl := Cslib.Probability.PMF.toOuterMeasure_toReal_add_compl p ({A.permanent} : Set F)
  rw [PMF.toOuterMeasure_apply_singleton] at hcompl
  have hcompl_set : ({A.permanent} : Set F)ᶜ = {y | y ≠ A.permanent} := rfl
  rw [hcompl_set] at hcompl
  linarith [toOuterMeasure_run_liptonPermanentTrial_ne_toReal_le ν hν O A]

/-- Real-valued form of `liptonPermanentTrial_prob_ge`: for `1 ≤ n` and
`#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`, the single-trial algorithm outputs `A.permanent`
with probability at least `1 - (n + 1) / (3 * n)`. -/
theorem liptonPermanentTrial_prob_toReal_ge (hn : 1 ≤ n) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ) / (3 * n) ≤
      (ProbComp.eval ((liptonPermanentTrial ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (3 * n) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have h3n : (0 : ℝ) < 3 * n := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      (n + 1 : ℝ) / (3 * n) := by
    rw [div_le_div_iff₀ hN h3n]
    nlinarith
  linarith [one_sub_le_eval_run_liptonPermanentTrial_toReal ν hν O A]

/-- Convenience form of `liptonPermanentTrial_prob_ge` under the textbook hypotheses `1 ≤ n` and
`3 * n < Fintype.card F`, using `Code.nonzeroNodes`. -/
theorem liptonPermanentTrial_prob_ge_of_three_mul_lt (hn : 1 ≤ n) (hcard : 3 * n < Fintype.card F)
    (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ≥0∞) / (3 * n : ℕ) ≤
      ProbComp.eval
        ((liptonPermanentTrial (Code.nonzeroNodes (add_two_le_card_of_three_mul_lt hn hcard)) A).run
          (fun M => pure (O M))) A.permanent :=
  liptonPermanentTrial_prob_ge _ (Code.nonzeroNodes_ne_zero _) O hO A

/-- Convenience form of `liptonPermanentTrial_prob_toReal_ge` under the textbook hypotheses
`1 ≤ n` and `3 * n < Fintype.card F`, using `Code.nonzeroNodes`. -/
theorem liptonPermanentTrial_prob_toReal_ge_of_three_mul_lt (hn : 1 ≤ n)
    (hcard : 3 * n < Fintype.card F) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (n + 1 : ℝ) / (3 * n) ≤
      (ProbComp.eval
        ((liptonPermanentTrial (Code.nonzeroNodes (add_two_le_card_of_three_mul_lt hn hcard)) A).run
          (fun M => pure (O M))) A.permanent).toReal :=
  liptonPermanentTrial_prob_toReal_ge hn _ (Code.nonzeroNodes_ne_zero _) O hO A

/-! ### Plurality amplification over `k` independent trials -/

/-- **Lipton's amplified random self-reduction for the permanent in the `ProbOracleComp`
query-complexity model** (after [Arora and Barak][AroraBarak09], Theorem 8.30).
Runs `k` independent trials of `liptonPermanentTrial ν A` and returns the plurality of their
outputs (defaulting to `0` when `k = 0`).

"With high probability" in Arora–Barak Theorem 8.30 is made precise here as error at most
`2^{-Ω(k)}` after `k` independent trials in `ProbOracleComp`; this is a precision choice on the
amplification wrapper. -/
noncomputable def liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    ProbOracleComp (PermanentOracleSpec n F) F :=
  plurality 0 <$> OracleComp.replicate k (liptonPermanentTrial ν A)

/-- Running `liptonPermanentPlurality k ν A` against a deterministic oracle `O` takes the plurality
of `k` independent runs of `liptonPermanentTrial ν A`. -/
theorem run_liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) (O : Matrix (Fin n) (Fin n) F → F) :
    (liptonPermanentPlurality k ν A).run (fun M => pure (O M)) =
      plurality 0 <$>
        OracleComp.replicate k ((liptonPermanentTrial ν A).run (fun M => pure (O M))) := by
  rw [liptonPermanentPlurality, ProbOracleComp.run_map, run_replicate]

/-- `liptonPermanentPlurality k ν A` makes at most `k * (n + 1)` oracle queries. -/
theorem isQueryBounded_liptonPermanentPlurality (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (A : Matrix (Fin n) (Fin n) F) :
    (liptonPermanentPlurality k ν A).IsQueryBounded (k * (n + 1)) :=
  (OracleComp.isCostBounded_map_iff _ _ _).mpr
    (isQueryBounded_replicate k (isQueryBounded_liptonPermanentTrial ν A))

/-- Every supported stateful execution of `liptonPermanentPlurality k ν A` makes exactly
`k * (n + 1)` external oracle queries. -/
theorem length_transcript_liptonPermanentPlurality {State : Type}
    (oracle : (M : Matrix (Fin n) (Fin n) F) → StateT State PMF F)
    (k : ℕ) (ν : Fin (n + 1) ↪ F) (A : Matrix (Fin n) (Fin n) F)
    {s s' : State} {result : F} {transcript : OracleComp.Transcript (PermanentOracleSpec n F)}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (liptonPermanentPlurality k ν A) (s, [])).support) :
    transcript.length = k * (n + 1) := by
  simp only [liptonPermanentPlurality, ProbOracleComp.runWith_map, PMF.mem_support_map_iff] at hmem
  obtain ⟨⟨xs, s₂, tr⟩, hxs, heq⟩ := hmem
  simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
  rcases heq with ⟨-, rfl, rfl⟩
  exact length_transcript_replicate oracle k (length_transcript_liptonPermanentTrial oracle ν A) hxs

/-- **General plurality corollary for Lipton's algorithm.** Whenever the single-trial error bound
`((n + 1) * #{M | O M ≠ M.permanent}) / |F|^{n²}` is at most `1 / 2 - γ` (for `0 ≤ γ`), the
`k`-trial plurality algorithm outputs `A.permanent` with probability at least
`1 - 2^{-(2 * γ² * k)}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_margin (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F) {γ : ℝ} (hγ : 0 ≤ γ)
    (hmargin : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - γ)
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-(2 * γ ^ 2 * k)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  rw [run_liptonPermanentPlurality]
  refine one_sub_two_rpow_le_eval_plurality_replicate_toReal 0 A.permanent k _ hγ ?_
  linarith [one_sub_le_eval_run_liptonPermanentTrial_toReal ν hν O A]

/-- **Plurality query-complexity bound under `|F|^{n²} / (3 * n)` error (after Arora–Barak
Theorem 8.30):** in the `ProbOracleComp` query-complexity model, for `3 ≤ n` and an oracle `O` with
`#{M | O M ≠ M.permanent} ≤ |F|^{n²} / (3 * n)`, the single trial succeeds with probability at least
`1 - (n + 1) / (3 * n) ≥ 5 / 9 = 1 / 2 + 1 / 18`, and the plurality of `k` independent trials
outputs `A.permanent` with probability at least `1 - 2^{-k / 162}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge (hn : 3 ≤ n) (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 162)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have h1 : 1 ≤ n := by omega
  have htrial := liptonPermanentTrial_prob_toReal_ge h1 ν hν O hO A
  have hn_real : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h3n_pos : (0 : ℝ) < 3 * n := by positivity
  have hfrac : (n + 1 : ℝ) / (3 * n) ≤ 4 / 9 := by
    rw [div_le_iff₀ h3n_pos]
    linarith
  rw [run_liptonPermanentPlurality, show -((k : ℝ) / 162) = -(2 * (1 / 18 : ℝ) ^ 2 * k) by ring]
  refine one_sub_two_rpow_le_eval_plurality_replicate_toReal 0 A.permanent k _ (by norm_num) ?_
  linarith

/-- `ℝ≥0∞`-valued form of `liptonPermanentPlurality_prob_toReal_ge` for `3 ≤ n`. -/
theorem liptonPermanentPlurality_prob_ge (hn : 3 ≤ n) (k : ℕ) (ν : Fin (n + 1) ↪ F)
    (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    ENNReal.ofReal (1 - (2 : ℝ) ^ (-((k : ℝ) / 162))) ≤
      ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M))) A.permanent := by
  rw [ENNReal.ofReal_le_iff_le_toReal (PMF.apply_ne_top _ _)]
  exact liptonPermanentPlurality_prob_toReal_ge hn k ν hν O hO A

/-- Convenience form of `liptonPermanentPlurality_prob_toReal_ge` under `3 ≤ n` and
`3 * n < Fintype.card F`, using `Code.nonzeroNodes`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_three_mul_lt (hn : 3 ≤ n)
    (hcard : 3 * n < Fintype.card F) (k : ℕ) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 162)) ≤
      (ProbComp.eval
        ((liptonPermanentPlurality k
          (Code.nonzeroNodes (add_two_le_card_of_three_mul_lt (by omega) hcard)) A).run
          (fun M => pure (O M))) A.permanent).toReal :=
  liptonPermanentPlurality_prob_toReal_ge hn k _ (Code.nonzeroNodes_ne_zero _) O hO A

/-- **Plurality corollary for `2 ≤ n` under `|F|^{n²} / (4 * n)` oracle error:**
each trial succeeds with probability at least `1 - (n + 1) / (4 * n) ≥ 5 / 8 = 1 / 2 + 1 / 8`, so
the plurality of `k` independent trials outputs `A.permanent` with probability at least
`1 - 2^{-k / 32}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_four_mul (hn : 2 ≤ n) (k : ℕ)
    (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (4 * n))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 32)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (4 * n) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have hn_real : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h4n : (0 : ℝ) < 4 * n := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - 1 / 8 := by
    have h1 : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
        (n + 1 : ℝ) / (4 * n) := by
      rw [div_le_div_iff₀ hN h4n]
      nlinarith
    have h2 : (n + 1 : ℝ) / (4 * n) ≤ 3 / 8 := by
      rw [div_le_iff₀ h4n]
      linarith
    linarith
  rw [show -((k : ℝ) / 32) = -(2 * (1 / 8 : ℝ) ^ 2 * k) by ring]
  exact liptonPermanentPlurality_prob_toReal_ge_of_margin k ν hν O (by norm_num) hdiv A

/-- **Plurality corollary for all `n` under `|F|^{n²} / (3 * (n + 1))` oracle error:**
each trial succeeds with probability at least `2 / 3 = 1 / 2 + 1 / 6`, so the plurality of `k`
independent trials outputs `A.permanent` with probability at least `1 - 2^{-k / 18}`. -/
theorem liptonPermanentPlurality_prob_toReal_ge_of_three_mul_succ (k : ℕ)
    (ν : Fin (n + 1) ↪ F) (hν : ∀ i, ν i ≠ 0) (O : Matrix (Fin n) (Fin n) F → F)
    (hO : #{M | O M ≠ M.permanent} ≤ Fintype.card F ^ (n * n) / (3 * (n + 1)))
    (A : Matrix (Fin n) (Fin n) F) :
    1 - (2 : ℝ) ^ (-((k : ℝ) / 18)) ≤
      (ProbComp.eval ((liptonPermanentPlurality k ν A).run (fun M => pure (O M)))
        A.permanent).toReal := by
  have hmul : (#{M | O M ≠ M.permanent} : ℝ) * (3 * (n + 1)) ≤ (Fintype.card F : ℝ) ^ (n * n) := by
    exact_mod_cast Nat.mul_le_of_le_div _ _ _ hO
  have hN : (0 : ℝ) < (Fintype.card F : ℝ) ^ (n * n) := by positivity
  have h3n : (0 : ℝ) < 3 * (n + 1) := by positivity
  have hdiv : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
      1 / 2 - 1 / 6 := by
    have h1 : ((n + 1) * #{M | O M ≠ M.permanent} : ℝ) / (Fintype.card F ^ (n * n) : ℝ) ≤
        (n + 1 : ℝ) / (3 * (n + 1)) := by
      rw [div_le_div_iff₀ hN h3n]
      nlinarith
    have h2 : (n + 1 : ℝ) / (3 * (n + 1)) = 1 / 3 := by
      have hn1 : (n + 1 : ℝ) ≠ 0 := by positivity
      field_simp
    linarith
  rw [show -((k : ℝ) / 18) = -(2 * (1 / 6 : ℝ) ^ 2 * k) by ring]
  exact liptonPermanentPlurality_prob_toReal_ge_of_margin k ν hν O (by norm_num) hdiv A

end Cslib.Complexity
