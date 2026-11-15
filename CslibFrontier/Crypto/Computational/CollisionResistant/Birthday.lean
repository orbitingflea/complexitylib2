/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Vector
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Exp
import CslibFrontier.Languages.Probabilistic.Oracle.Vector
import CslibFrontier.Probability.IID.FunctionCollision
import CslibFrontier.Probability.PMF.Event

/-!
# The birthday collision finder

`birthdayFinder digest sampler s` samples `s` messages, computes the digest of each with the
oracle program `digest`, and returns the first pair of different messages with equal digests
([BonehShoup2023], §8.3, Algorithm BirthdayAttack, printed p. 294). It reaches the function being
attacked only through its oracle, so a bound on its oracle calls is a bound on evaluations of that
function.

* **Cost.** When each digest makes at most `c` oracle calls, the finder makes at most `s * c` on
  every path (`isQueryBounded_birthdayFinder`). This counts oracle calls, the cost measure of §8.3.
  It is not a running time: sampling and the search among the `s` digests, which compares up to
  `s ^ 2` pairs, are not counted, and no machine model is involved. It is a worst-case count, not an
  expected cost.
* **Success.** Run against a deterministic oracle under which `digest m` returns `f m`, with
  uniform messages, the finder returns a collision of `f` with probability at least
  `1 - exp (-s (s - 1) / (2 |D|)) - C(s, 2) / |M|`, where `D` contains every value of `f`
  (`birthdayFinder_success`), and at least `1/2` with the book's parameters `|M| ≥ 100 |D|` and
  `s = ⌈2 √|D|⌉ + 1` (`birthdayFinder_success_book`). Nothing is assumed about `f` beyond
  `D`. It never returns a pair that is not a collision (`birthdayFinder_sound`).

## Differences from [BonehShoup2023]

* Lemma 8.2 is about the messages the algorithm samples. Here it is a statement about the output
  of the program `birthdayFinder`, which samples them; the probabilistic part is
  `Cslib.Probability.PMF.one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision`,
  whose docstring lists the differences in the proof.
* Steps 4 and 5 of Algorithm BirthdayAttack look for two positions with equal digests and then
  test whether their messages differ. `collidingPair?` returns the first pair of positions, in
  lexicographic order, with equal digests and different messages, so the finder succeeds exactly
  on the event of Lemma 8.2.
* The algorithm fixes `s = ⌈2 √N⌉ + 1`. The finder takes `s` as a parameter, and
  `birthdayFinder_success_book` instantiates the book's value.
* The book counts evaluations of `H`. Here `digest m` is any oracle program, and the count is of
  its oracle calls. The book's `O(√N)` memory is not stated.

## Main definitions

* `Cslib.Crypto.collidingPair?`: the first pair of different messages with equal digests.
* `Cslib.Crypto.birthdayFinder`: the birthday collision finder.
* `Cslib.Crypto.collisionOutputs`: the outputs that are collisions of a function.

## Main results

* `Cslib.Crypto.isQueryBounded_birthdayFinder`: the finder makes at most `s * c` oracle calls.
* `Cslib.Crypto.eval_run_birthdayFinder`: against a deterministic oracle, the finder samples and
  searches.
* `Cslib.Crypto.birthdayFinder_sound`: every output other than `none` is a collision.
* `Cslib.Crypto.birthdayFinder_success`, `Cslib.Crypto.birthdayFinder_success_book`: the success
  probability ([BonehShoup2023], Lemma 8.2).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §8.3, Algorithm BirthdayAttack and Lemma 8.2 (printed
  pp. 294–295).
-/

public section

namespace Cslib.Crypto

open Cslib.Probability.PMF

section Search

variable {M T : Type} [DecidableEq M] [DecidableEq T]

/-- The first pair of positions (in lexicographic order) whose digests agree and whose messages
differ, returned as the two messages and their common digest. -/
@[expose] def collidingPair? {s : ℕ} (ms : Fin s → M) (ds : Fin s → T) : Option (M × M × T) :=
  ((List.finRange s ×ˢ List.finRange s).find? fun p => ds p.1 = ds p.2 ∧ ms p.1 ≠ ms p.2).map
    fun p => (ms p.1, ms p.2, ds p.1)

/-- An output `some (m, m', d)` of `collidingPair?` is two different messages that occur among
`ms` with digest `d`. -/
theorem collidingPair?_eq_some {s : ℕ} {ms : Fin s → M} {ds : Fin s → T} {m m' : M} {d : T}
    (h : collidingPair? ms ds = some (m, m', d)) :
    m ≠ m' ∧ ∃ i j, ms i = m ∧ ms j = m' ∧ ds i = d ∧ ds j = d := by
  obtain ⟨p, hp, heq⟩ := Option.map_eq_some_iff.mp h
  have hp' := List.find?_some hp
  simp only [decide_eq_true_eq] at hp'
  simp only [Prod.mk.injEq] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  exact ⟨hp'.2, p.1, p.2, rfl, rfl, rfl, hp'.1.symm⟩

/-- `collidingPair?` finds a pair exactly when two positions have equal digests and different
messages. -/
theorem isSome_collidingPair?_iff {s : ℕ} {ms : Fin s → M} {ds : Fin s → T} :
    (collidingPair? ms ds).isSome ↔ ∃ i j, ds i = ds j ∧ ms i ≠ ms j := by
  simp [collidingPair?]

end Search

section Finder

variable {Query M T : Type} {spec : Query → Type} [DecidableEq M] [DecidableEq T]

/-- The birthday collision finder ([BonehShoup2023], §8.3, Algorithm BirthdayAttack, printed
p. 294, with the number of samples `s` as a parameter): sample `s` messages, compute the digest of
each with the oracle program `digest`, and return the first pair of different messages with equal
digests, together with the digest. -/
def birthdayFinder (digest : M → ProbOracleComp spec T) (sampler : ProbComp M) (s : ℕ) :
    ProbOracleComp spec (Option (M × M × T)) :=
  ProbOracleComp.sample (OracleComp.replicateFin s sampler) >>= fun ms =>
    OracleComp.pi (fun i : Fin s => digest (ms i)) >>= fun ds =>
      pure (collidingPair? ms ds)

/-- **Cost of the birthday finder.** When each digest makes at most `c` oracle calls, the finder
makes at most `s * c` on every path. Sampling and the search among the digests are not counted:
this is a count of oracle calls, not a running time. -/
theorem isQueryBounded_birthdayFinder {digest : M → ProbOracleComp spec T} {c : ℕ}
    (hdigest : ∀ m, ProbOracleComp.IsQueryBounded (digest m) c) (sampler : ProbComp M) (s : ℕ) :
    ProbOracleComp.IsQueryBounded (birthdayFinder digest sampler s) (s * c) := by
  have h := (ProbOracleComp.IsQueryBounded.sample (spec := spec)
    (OracleComp.replicateFin s sampler)).bind (m := s * c + 0) fun ms =>
      (OracleComp.isCostBounded_pi fun i => hdigest (ms i)).bind fun ds =>
        OracleComp.IsCostBounded.pure (collidingPair? ms ds) 0
  simpa [birthdayFinder] using h

/-- Against a deterministic oracle `O` under which `digest m` returns `f m`, the finder samples
and searches. -/
theorem eval_run_birthdayFinder {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) (hdigest : ∀ m, (digest m).run (fun x => pure (O x)) = pure (f m))
    (sampler : ProbComp M) (s : ℕ) :
    ProbComp.eval ((birthdayFinder digest sampler s).run fun x => pure (O x)) =
      (ProbComp.eval (OracleComp.replicateFin s sampler)).map
        fun ms => collidingPair? ms fun i => f (ms i) := by
  simp only [birthdayFinder, ProbOracleComp.run_bind, ProbOracleComp.run_sample,
    ProbOracleComp.run_pi, hdigest, ProbOracleComp.run_pure, ProbComp.eval_bind,
    ProbComp.eval_pi_pure, ProbComp.eval_pure, PMF.pure_bind]
  rfl

/-- The outputs of the finder that are collisions of `f`: two different messages and their
common value. -/
@[expose] def collisionOutputs (f : M → T) : Set (Option (M × M × T)) :=
  {o | ∃ m m', m ≠ m' ∧ f m' = f m ∧ o = some (m, m', f m)}

/-- The finder never returns a wrong pair: against a deterministic oracle under which `digest m`
returns `f m`, every output other than `none` is a collision of `f`, for every sampler. -/
theorem birthdayFinder_sound {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) (hdigest : ∀ m, (digest m).run (fun x => pure (O x)) = pure (f m))
    (sampler : ProbComp M) (s : ℕ) {o : Option (M × M × T)}
    (ho : o ∈ (ProbComp.eval ((birthdayFinder digest sampler s).run
      fun x => pure (O x))).support) (hne : o ≠ none) : o ∈ collisionOutputs f := by
  rw [eval_run_birthdayFinder O f hdigest, PMF.support_map] at ho
  obtain ⟨ms, -, rfl⟩ := ho
  obtain ⟨⟨m, m', d⟩, hc⟩ := Option.ne_none_iff_exists'.mp hne
  obtain ⟨hmm, i, j, rfl, rfl, rfl, hd⟩ := collidingPair?_eq_some hc
  exact ⟨_, _, hmm, hd, hc⟩

variable [Fintype M] [Nonempty M]

/-- **Success probability of the birthday finder** ([BonehShoup2023], §8.3, Lemma 8.2, printed
p. 294, with explicit error terms). Against a deterministic oracle under which `digest m` returns
`f m`, with `s` uniform messages, the finder returns a collision of `f` with probability at least
`1 - exp (-s (s - 1) / (2 |D|)) - C(s, 2) / |M|`, where `D` contains every value of `f`. -/
theorem birthdayFinder_success {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) (hdigest : ∀ m, (digest m).run (fun x => pure (O x)) = pure (f m))
    (D : Finset T) (hf : ∀ m, f m ∈ D) (s : ℕ) :
    1 - Real.exp (-(s * (s - 1) / (2 * D.card))) - s.choose 2 * (Fintype.card M : ℝ)⁻¹ ≤
      ((ProbComp.eval ((birthdayFinder digest (ProbComp.uniform M) s).run
        fun x => pure (O x))).toOuterMeasure (collisionOutputs f)).toReal := by
  have hlaw : ProbComp.eval (OracleComp.replicateFin s (ProbComp.uniform M)) =
      iid (uniformOfFintype M) s := by
    rw [iid_uniformOfFintype]
    exact ProbComp.eval_pi_uniform
  rw [eval_run_birthdayFinder O f hdigest, PMF.toOuterMeasure_map_apply, hlaw]
  refine (one_sub_exp_neg_sub_choose_le_iid_uniformOfFintype_exists_collision f D hf s).trans
    (ENNReal.toReal_mono (toOuterMeasure_ne_top _ _) (MeasureTheory.measure_mono ?_))
  rintro x ⟨i, j, hd, hm⟩
  obtain ⟨⟨m, m', d⟩, ho⟩ := Option.isSome_iff_exists.mp
    ((isSome_collidingPair?_iff (ds := fun i => f (x i))).mpr ⟨i, j, hd, hm⟩)
  obtain ⟨hne, i', j', rfl, rfl, rfl, hd'⟩ := collidingPair?_eq_some ho
  exact ⟨_, _, hne, hd', ho⟩

/-- **Lemma 8.2 with the book's parameters** ([BonehShoup2023], §8.3, printed p. 294): if
`|M| ≥ 100 |D|`, where `D` contains every value of `f`, then the finder with
`s = ⌈2 √|D|⌉ + 1` uniform messages returns a collision of `f` with probability at least `1/2`.
With `isQueryBounded_birthdayFinder` it makes `s` digest computations. -/
theorem birthdayFinder_success_book {digest : M → ProbOracleComp spec T} (O : (q : Query) → spec q)
    (f : M → T) (hdigest : ∀ m, (digest m).run (fun x => pure (O x)) = pure (f m))
    (D : Finset T) (hf : ∀ m, f m ∈ D) (hM : 100 * D.card ≤ Fintype.card M) :
    (1 / 2 : ℝ) ≤
      ((ProbComp.eval ((birthdayFinder digest (ProbComp.uniform M)
        (⌈2 * Real.sqrt (D.card : ℝ)⌉₊ + 1)).run
          fun x => pure (O x))).toOuterMeasure (collisionOutputs f)).toReal :=
  (half_le_one_sub_exp_neg_sub_choose_of_hundred_mul_le
    (Finset.card_pos.mpr ⟨_, hf (Classical.arbitrary M)⟩) hM).trans
      (birthdayFinder_success O f hdigest D hf _)

end Finder

end Cslib.Crypto
