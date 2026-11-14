/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import CslibFrontier.Languages.Probabilistic.Vector

/-!
# Running and counting queries of `OracleComp.pi` and `OracleComp.replicate`

Execution (`ProbOracleComp.run`), syntactic query bounds (`ProbOracleComp.IsQueryBounded`), and
exact stateful transcript lengths (`OracleComp.withTranscript`) for finite tuples (`OracleComp.pi`)
and independent repetitions (`OracleComp.replicate`) of probabilistic oracle computations.

## Main results

* `Cslib.ProbOracleComp.run_pi`, `Cslib.ProbOracleComp.run_pi_query`: running `OracleComp.pi`
  against a probabilistic or deterministic oracle.
* `Cslib.ProbOracleComp.isQueryBounded_pi_query`,
  `Cslib.ProbOracleComp.length_transcript_pi_query`: a tuple of `m` external queries makes at most
  `m` (and on every supported transcript, exactly `m`) external queries.
* `Cslib.ProbOracleComp.run_replicate`: running `OracleComp.replicate k program` against an oracle
  repeats `ProbOracleComp.run program O`.
* `Cslib.ProbOracleComp.isQueryBounded_replicate`,
  `Cslib.ProbOracleComp.length_transcript_replicate`: repeating a `q`-query computation `k` times
  makes at most `k * q` (and on every supported transcript, exactly `k * q`) external queries.
-/

public section

namespace Cslib.ProbOracleComp

variable {Query α : Type} {spec : Query → Type}

/-- Running `OracleComp.pi` against an oracle runs each coordinate program in order. -/
theorem run_pi {m : ℕ} {β : Fin m → Type}
    (programs : (i : Fin m) → ProbOracleComp spec (β i))
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.pi programs) O =
      OracleComp.pi (fun i => ProbOracleComp.run (programs i) O) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_map,
      ih (fun i => programs i.succ)]

/-- Running a tuple of external queries against a deterministic oracle returns the tuple of
answers. -/
theorem run_pi_query {m : ℕ} (q : Fin m → Query) (O : (x : Query) → spec x) :
    ProbOracleComp.run
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
      (fun x => pure (O x)) = pure (fun i => O (q i)) := by
  induction m with
  | zero =>
    change (pure (fun i : Fin 0 => i.elim0) : ProbComp ((i : Fin 0) → spec (q i))) = _
    congr 1
    funext i
    exact i.elim0
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.run_bind, ProbOracleComp.run_query,
      ProbOracleComp.run_map, ih (fun i => q i.succ), pure_bind, map_pure]
    congr 1
    funext i
    exact Fin.cases rfl (fun _ => rfl) i

/-- A tuple of `m` external queries makes at most `m` external queries. -/
theorem isQueryBounded_pi_query {m : ℕ} (q : Fin m → Query) :
    ProbOracleComp.IsQueryBounded
      (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i))) m := by
  induction m with
  | zero => exact OracleComp.IsCostBounded.pure _ 0
  | succ m ih =>
    rw [OracleComp.pi_succ]
    refine OracleComp.IsCostBounded.mono (n := 1 + m) ?_ (by omega)
    refine (ProbOracleComp.IsQueryBounded.query (q 0)).bind fun _ => ?_
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (ih (fun i => q i.succ))

/-- Every supported stateful execution of a tuple of `m` external queries logs a transcript of
exact length `m`. -/
theorem length_transcript_pi_query {m : ℕ} {State : Type}
    (oracle : (q : Query) → StateT State PMF (spec q)) (q : Fin m → Query)
    {s s' : State} {result : (i : Fin m) → spec (q i)}
    {transcript : OracleComp.Transcript spec}
    (hmem : (result, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.pi (fun i : Fin m => ProbOracleComp.query (spec := spec) (q i)))
        (s, [])).support) :
    transcript.length = m := by
  induction m generalizing s s' transcript with
  | zero =>
    simp only [OracleComp.pi_zero, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, rfl⟩
    rfl
  | succ m ih =>
    simp only [OracleComp.pi_succ, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_map, PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨⟨first, s₁, seen⟩, hfirst, ⟨rest, s₂, total⟩, hrest, heq⟩ := hmem
    simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
    rcases heq with ⟨-, rfl, rfl⟩
    simp only [OracleComp.withTranscript, PMF.mem_support_map_iff] at hfirst
    obtain ⟨⟨ans, next⟩, -, hfirst_eq⟩ := hfirst
    cases hfirst_eq
    rw [ProbOracleComp.run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
    obtain ⟨⟨rest', final, fresh⟩, hfresh, hrest_eq⟩ := hrest
    cases hrest_eq
    have hlen := ih (fun i => q i.succ) hfresh
    simp [hlen]

/-- Running `OracleComp.replicate` against an oracle repeats the run of the underlying program. -/
@[simp]
theorem run_replicate (k : ℕ) (program : ProbOracleComp spec α)
    (O : (q : Query) → ProbComp (spec q)) :
    ProbOracleComp.run (OracleComp.replicate k program) O =
      OracleComp.replicate k (ProbOracleComp.run program O) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp [OracleComp.replicate_succ, ih]

/-- Repeating a `q`-query-bounded program `k` times makes at most `k * q` queries. -/
theorem isQueryBounded_replicate (k : ℕ) {program : ProbOracleComp spec α} {q : ℕ}
    (hq : program.IsQueryBounded q) :
    ProbOracleComp.IsQueryBounded (OracleComp.replicate k program) (k * q) := by
  induction k with
  | zero =>
    rw [Nat.zero_mul]
    exact OracleComp.IsCostBounded.pure _ 0
  | succ k ih =>
    rw [OracleComp.replicate_succ]
    refine OracleComp.IsCostBounded.mono (n := q + k * q) ?_ (by simp [Nat.succ_mul, Nat.add_comm])
    refine hq.bind fun _ => ?_
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr ih

/-- If every supported execution of `program` makes exactly `q` external queries, then every
supported execution of `OracleComp.replicate k program` makes exactly `k * q` external queries. -/
theorem length_transcript_replicate {State : Type}
    (oracle : (x : Query) → StateT State PMF (spec x)) (k : ℕ)
    {program : ProbOracleComp spec α} {q : ℕ}
    (hq : ∀ {s s' : State} {result : α} {tr : OracleComp.Transcript spec},
      (result, s', tr) ∈
        (ProbOracleComp.runWith (OracleComp.withTranscript oracle) program (s, [])).support →
        tr.length = q)
    {s s' : State} {results : List α} {transcript : OracleComp.Transcript spec}
    (hmem : (results, s', transcript) ∈
      (ProbOracleComp.runWith (OracleComp.withTranscript oracle)
        (OracleComp.replicate k program) (s, [])).support) :
    transcript.length = k * q := by
  induction k generalizing s s' results transcript with
  | zero =>
    simp only [OracleComp.replicate_zero, ProbOracleComp.runWith_pure, PMF.mem_support_pure_iff,
      Prod.mk.injEq] at hmem
    rcases hmem with ⟨-, -, rfl⟩
    simp
  | succ k ih =>
    simp only [OracleComp.replicate_succ, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_map,
      PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at hmem
    obtain ⟨⟨first, s₁, seen⟩, hfirst, ⟨rest, s₂, total⟩, hrest, heq⟩ := hmem
    simp only [Prod.map, id_eq, Prod.mk.injEq] at heq
    rcases heq with ⟨-, rfl, rfl⟩
    rw [ProbOracleComp.run_interpret_withTranscript_append, PMF.mem_support_map_iff] at hrest
    obtain ⟨⟨rest', final, fresh⟩, hfresh, hrest_eq⟩ := hrest
    cases hrest_eq
    have h1 := hq hfirst
    have h2 := ih hfresh
    simp [h1, h2, Nat.succ_mul, Nat.add_comm]

end Cslib.ProbOracleComp
