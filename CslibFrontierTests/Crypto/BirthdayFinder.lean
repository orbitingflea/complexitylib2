/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.CollisionResistant.Birthday
import CslibFrontier.Foundations.Analysis.SpecialFunctions.ExpBounds
import CslibFrontier.Foundations.Data.BitString.Basic
import CslibFrontier.Probability.IID.FunctionCollision

/-!
# Tests for the birthday collision finder

Checks for `CslibFrontier/Crypto/Computational/CollisionResistant/Birthday.lean` and
`CslibFrontier/Probability/IID/FunctionCollision.lean` as a `module` client with ordinary imports:

* `collidingPair?` on numbers: the first pair in position order, equal messages that are not a
  collision, and no collision; injective digests and constant messages never give a pair.
* The cost certificate for the finder that queries its oracle once per sample.
* With one sample the finder returns `none`; every pair it returns is two different bytes with one
  value.
* Lemma 8.2 on bytes: for every `O : BitString 8 → Bool`, five samples give a collision with
  probability at least `119/128`, and the book's sample count `⌈2 √2⌉ + 1` gives at least `1/2`.
* The hypothesis `100 * D.card ≤ Fintype.card M` of `birthdayFinder_success_book` cannot be
  dropped: an injective digest has no collision.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.BirthdayFinder

open Cslib Cslib.Crypto

/-! ## The search -/

example : collidingPair? ![(0 : ℕ), 1, 2, 1] ![(5 : ℕ), 7, 5, 7] = some (0, 2, 5) := by decide

/-- Equal digests that come from equal messages are not a collision. -/
example : collidingPair? ![(1 : ℕ), 1] ![(7 : ℕ), 7] = none := by decide

example : collidingPair? ![(1 : ℕ), 2, 3] ![(7 : ℕ), 8, 9] = none := by decide

/-- Injective digests give no pair. -/
example {s : ℕ} (ms : Fin s → ℕ) {ds : Fin s → ℕ} (hd : Function.Injective ds) :
    collidingPair? ms ds = none := by
  rw [← Option.not_isSome_iff_eq_none, isSome_collidingPair?_iff]
  rintro ⟨i, j, hij, hm⟩
  exact hm (congrArg ms (hd hij))

/-- Constant messages give no pair, whatever the digests. -/
example {s : ℕ} (m : ℕ) (ds : Fin s → ℕ) : collidingPair? (fun _ => m) ds = none := by
  cases h : collidingPair? (fun _ : Fin s => m) ds with
  | none => rfl
  | some p =>
    obtain ⟨m₁, m₂, d⟩ := p
    obtain ⟨hne, i, j, rfl, rfl, -, -⟩ := collidingPair?_eq_some h
    exact absurd rfl hne

/-! ## The finder on bytes

The finder below asks its oracle for the value of each sampled byte. -/

/-- The finder that queries its oracle once per byte. -/
noncomputable abbrev byteFinder (s : ℕ) :
    ProbOracleComp (fun _ : BitString 8 => Bool) (Option (BitString 8 × BitString 8 × Bool)) :=
  birthdayFinder (fun m => ProbOracleComp.query m) (ProbComp.uniform (BitString 8)) s

/-- The certificate: `s` samples cost at most `s` oracle calls. -/
example (s : ℕ) : ProbOracleComp.IsQueryBounded (byteFinder s) s := by
  simpa using isQueryBounded_birthdayFinder (fun m => ProbOracleComp.IsQueryBounded.query m) _ s

/-- One sample cannot collide: the finder with `s = 1` returns `none`. -/
example (O : BitString 8 → Bool) :
    ProbComp.eval ((byteFinder 1).run fun x => pure (O x)) = PMF.pure none := by
  have h : ∀ ms : Fin 1 → BitString 8, collidingPair? ms (fun i => O (ms i)) = none := by
    intro ms
    rw [← Option.not_isSome_iff_eq_none, isSome_collidingPair?_iff]
    rintro ⟨i, j, -, hm⟩
    exact hm (congrArg ms (Subsingleton.elim i j))
  rw [eval_run_birthdayFinder O O (fun m => ProbOracleComp.run_query _ _)]
  simp only [h]
  exact PMF.map_const _ _

/-- Every pair the finder returns is two different bytes with the value it reports. -/
example (O : BitString 8 → Bool) (s : ℕ) {m m' : BitString 8} {d : Bool}
    (ho : some (m, m', d) ∈ (ProbComp.eval ((byteFinder s).run fun x => pure (O x))).support) :
    m ≠ m' ∧ O m = d ∧ O m' = d := by
  have hc := birthdayFinder_sound O O (fun m => ProbOracleComp.run_query _ _) _ s ho (by simp)
  simp only [collisionOutputs, Set.mem_ofPred_eq, Option.some.injEq, Prod.mk.injEq] at hc
  obtain ⟨a, a', hne, heq, rfl, rfl, rfl⟩ := hc
  exact ⟨hne, rfl, heq⟩

/-- Lemma 8.2 with explicit error terms on bytes: for every predicate `O`, five samples give two
different bytes with one value with probability at least `1 - 1/32 - 10/256 = 119/128`. -/
example (O : BitString 8 → Bool) :
    (119 / 128 : ℝ) ≤
      ((ProbComp.eval ((byteFinder 5).run fun x => pure (O x))).toOuterMeasure
        (collisionOutputs O)).toReal := by
  refine le_trans ?_ (birthdayFinder_success O O (fun m => ProbOracleComp.run_query _ _)
    Finset.univ (fun _ => Finset.mem_univ _) 5)
  have he : Real.exp (-(((5 : ℕ) : ℝ) * (((5 : ℕ) : ℝ) - 1) /
      (2 * ((Finset.univ : Finset Bool).card : ℝ)))) ≤ 1 / 32 := by
    refine (Real.exp_le_half_pow 5 ?_).trans_eq (by norm_num)
    simp only [Finset.card_univ, Fintype.card_bool]
    norm_num
  have hc : ((Nat.choose 5 2 : ℕ) : ℝ) * ((Fintype.card (BitString 8) : ℕ) : ℝ)⁻¹ = 10 / 256 := by
    rw [BitString.card]
    norm_num [Nat.choose]
  rw [hc]
  linarith

/-- Lemma 8.2 with the book's sample count: for every predicate `O` on bytes, `⌈2 √2⌉ + 1`
samples give two different bytes with one value with probability at least `1/2`. Here
`|M| = 256 ≥ 100 * 2`. -/
example (O : BitString 8 → Bool) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((byteFinder
        (⌈2 * Real.sqrt ((Finset.univ : Finset Bool).card : ℝ)⌉₊ + 1)).run
          fun x => pure (O x))).toOuterMeasure (collisionOutputs O)).toReal :=
  birthdayFinder_success_book O O (fun m => ProbOracleComp.run_query _ _) Finset.univ
    (fun _ => Finset.mem_univ _) (by rw [BitString.card]; decide)

/-- `|M| ≥ 100 N` cannot be dropped from `birthdayFinder_success_book`: an injective digest has
no collision, so the finder never succeeds. -/
example : collisionOutputs (id : Bool → Bool) = ∅ := by
  ext o
  simp only [collisionOutputs, id, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨m, m', hne, heq, -⟩
  exact hne heq.symm

/-! ## Collisions of a function on uniform samples -/

/-- The bound of `one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision` for a
predicate on bytes, as a statement about the samples alone. -/
example (O : BitString 8 → Bool) (s : ℕ) :
    1 - Real.exp (-(s * (s - 1) / (2 * 2))) - s.choose 2 * (256 : ℝ)⁻¹ ≤
      ((Cslib.Probability.PMF.iid (Cslib.Probability.PMF.uniformOfFintype (BitString 8))
        s).toOuterMeasure {x | ∃ i j, O (x i) = O (x j) ∧ x i ≠ x j}).toReal := by
  have h :=
    Cslib.Probability.PMF.one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision O
      Finset.univ (fun _ => Finset.mem_univ _) s
  rw [Finset.card_univ, Fintype.card_bool, BitString.card] at h
  norm_num at h ⊢
  exact h

/-- The book's parameters for `N = 2` and `K = 256`. -/
example : (1 / 2 : ℝ) ≤ 1 - Real.exp (-(((⌈2 * Real.sqrt 2⌉₊ + 1 : ℕ) : ℝ) *
    (((⌈2 * Real.sqrt 2⌉₊ + 1 : ℕ) : ℝ) - 1) / (2 * 2))) -
      (⌈2 * Real.sqrt 2⌉₊ + 1).choose 2 * (256 : ℝ)⁻¹ := by
  exact_mod_cast
    Cslib.Probability.PMF.half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le (N := 2) (K := 256)
      (by norm_num) (by norm_num)

end CslibFrontierTests.BirthdayFinder
