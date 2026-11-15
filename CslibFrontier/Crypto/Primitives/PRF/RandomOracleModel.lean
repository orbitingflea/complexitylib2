/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Foundations.Data.BitString
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Foundations.Data.BitString.ShortWords
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.UniformExtend

/-!
# Pseudorandom functions in the random-oracle model

Attack Game 8.4 of [BonehShoup2023], Section 8.10.2 (printed p. 329), for finite types. The
adversary is one adaptive program with private coins and two interfaces (`ROSpec`): the query
`Sum.inl x` asks for the keyed function `F` at `x : X` and returns a value in `Y`, and the query
`Sum.inr m` asks for the random oracle at `m : M` and returns a value in `T`. Both experiments first
sample the whole oracle table `O : M → T` uniformly and answer every oracle query `m` with `O m`.
Experiment 0 (`roRealExperiment F A`) then samples one uniform key and answers every `F`-query `x`
with `F O key x`; Experiment 1 (`roIdealExperiment A`) samples one uniform function `f : X → Y` and
answers with `f x`. The advantage `roAdvantage F A` is their distinguishing advantage. A keyed
function `F : (M → T) → Key → X → Y` of the oracle table is the book's `F^O`. When `F` ignores the
table and the adversary never queries the oracle, this is Attack Game 4.2
(`roAdvantage_const_simulate`).

Theorem 8.9 is about the key-prepending function `F_pre(k, x) = H (k ‖ x)`, here
`prependKey encode O key x = O (encode key x)` for a pairing `encode : Key → X → M`. If `encode`
is injective in the pair of its arguments, an adversary that makes at most `Q` random-oracle
queries on every path has advantage at most `Q / |Key|` (`roAdvantage_prependKey_le`). Nothing is
assumed about its `F`-queries, its private coins or its running time, as in the book's remark that
the theorem is unconditional. `keyAppend κ L` is the book's `k ‖ x` for a `κ`-bit key and a word
of length at most `L`, with bound `Q / 2 ^ κ` (`roAdvantage_prependKey_keyAppend_le`). Over a
security parameter, if `1 / |Key n|` is negligible (for bit strings: keys of at least `n` bits),
every family of adversaries with polynomially many random-oracle queries has negligible advantage
(`negligible_roAdvantage_prependKey`, `negligible_roAdvantage_prependKey_keyAppend`).

The proof is not the book's, which uses lazily sampled "faithful" and "forgetful gnome" games
(p. 330) and assumes that the adversary never repeats an `F`-query. For a fixed key the
oracle `O` has the law of `Function.extend (encode key) f O` for an independent uniform table
`f : X → T` (`Cslib.Probability.PMF.uniformOfFintype_bind_bind_extend`), and this oracle composed
with `encode key` is `f`. Experiment 0 therefore has the law of a game that answers `F`-queries with
`f` and oracle queries with `Function.extend (encode key) f O`, while Experiment 1 answers oracle
queries with `O`. For fixed `f` and `O` the two challengers differ only at an oracle query
`encode key x`, so they are identical until the set of keys that the oracle queries name contains
the key (`ProbOracleComp.IdenticalUntilBad`). In Experiment 1 that set does not depend on the key
and has at most `Q` members on every path, so a uniform key lies in it with probability at most
`Q / |Key|`.

Differences from the book:

* All of `Key`, `X`, `Y`, `M` and `T` are finite types, and the oracle is one uniform table.
* A pairing `encode` that is injective in the pair (`Function.Injective2 encode`) replaces `k ‖ x`;
  both halves of injectivity are needed. In the bit-string instance `M` is exactly the words of
  length at most `κ + L`, where the book's `M` only includes them.
* In Theorem 8.9 the output type of `F_pre` is the oracle's, `Y = T`, as in the book.
* `Q` bounds the random-oracle queries on every path, whatever the coins and the replies; repeated
  queries are allowed and counted.
* The asymptotic statements index everything by `n : ℕ` and bound the number of random-oracle
  queries by a polynomial; they do not mention running time. Definition 8.5 is not a named
  predicate.
* Not stated: that the same construction is insecure for a Merkle–Damgård hash function (the
  book's "But wait!", p. 329), and Section 8.10.3.

`ROSpec`, `ROAdversary`, `roRealExperiment`, `roIdealExperiment`, `roAdvantage`, `prependKey` and
`keyAppend` are this library's names. `Cslib.Crypto.Protocols.FujisakiOkamoto` has its own `ROSpec`
and `ROAdversary`.

## Main definitions

* `Cslib.Crypto.PRF.ROSpec`, `Cslib.Crypto.PRF.ROAdversary`: the two interfaces and the adversary.
* `Cslib.Crypto.PRF.ROAdversary.IsOracleQueryBounded`: at most `Q` random-oracle queries on every
  path; `F`-queries and private samples are free.
* `Cslib.Crypto.PRF.roRealExperiment`, `Cslib.Crypto.PRF.roIdealExperiment`,
  `Cslib.Crypto.PRF.roAdvantage`: Attack Game 8.4 and its advantage.
* `Cslib.Crypto.PRF.prependKey`: the key-prepending function `F_pre`.
* `Cslib.Crypto.PRF.keyAppend`: a `κ`-bit key followed by a word of length at most `L`.

## Main results

* `Cslib.Crypto.PRF.ROAdversary.IsOracleQueryBounded.of_isQueryBounded`: a budget on all queries
  bounds the random-oracle queries.
* `Cslib.Crypto.PRF.eval_roRealExperiment`, `Cslib.Crypto.PRF.eval_roIdealExperiment`: the laws of
  the two experiments at the `PMF` level.
* `Cslib.Crypto.PRF.roAdvantage_const_simulate`: the game restricts to Attack Game 4.2.
* `Cslib.Crypto.PRF.roAdvantage_prependKey_le`: Theorem 8.9, the bound `Q / |Key|`.
* `Cslib.Crypto.PRF.negligible_roAdvantage_prependKey`: Theorem 8.9 over a security parameter.
* `Cslib.Crypto.PRF.keyAppend_injective2`, `Cslib.Crypto.PRF.roAdvantage_prependKey_keyAppend_le`,
  `Cslib.Crypto.PRF.negligible_roAdvantage_prependKey_keyAppend`: the book's bit strings.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*, Version 0.6][BonehShoup2023],
  Section 8.10.2, Attack Game 8.4, Definition 8.5 and Theorem 8.9 (printed p. 329), and the
  proof of Theorem 8.9 (printed p. 330).
-/

public section

namespace Cslib.Crypto.PRF

open Probability
open Cslib.Probability.PMF (uniformOfFintype)
open scoped NNReal ENNReal

variable {Key X Y M T : Type}

/-! ### Attack Game 8.4 -/

/-- The calls of a PRF adversary in the random-oracle model: an `F`-query names a point of `X` and
returns a value in `Y`; an `O`-query names a point of `M` and returns a value in `T`. -/
abbrev ROSpec (X Y M T : Type) : OracleSpec (X ⊕ M) := (fun _ : X => Y) ⊕ₒ (fun _ : M => T)

/-- An adaptive test with private coins and oracle access to a function `X → Y` and to the random
oracle `M → T`. -/
abbrev ROAdversary (X Y M T : Type) := ProbOracleComp (ROSpec X Y M T) Bool

/-- The adversary makes at most `Q` random-oracle queries on every path, whatever its private
samples and the replies. Its `F`-queries and its private samples are free. -/
abbrev ROAdversary.IsOracleQueryBounded (A : ROAdversary X Y M T) (Q : ℕ) : Prop :=
  OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) A Q

/-- Experiment 0 of Attack Game 8.4: sample the random oracle `O` and one uniform key, answer every
`F`-query `x` with `F O key x` and every `O`-query `m` with `O m`. -/
noncomputable def roRealExperiment [Fintype M] [DecidableEq M] [Fintype T] [Nonempty T]
    [Fintype Key] [Nonempty Key] (F : (M → T) → Key → X → Y) (A : ROAdversary X Y M T) :
    ProbComp Bool := do
  let O ← ProbComp.uniform (M → T)
  let key ← ProbComp.uniform Key
  A.run (OracleComp.sumHandler (fun x => pure (F O key x)) (fun m => pure (O m)))

/-- Experiment 1 of Attack Game 8.4: sample the random oracle `O` and one uniform function
`f : X → Y`, answer every `F`-query `x` with `f x` and every `O`-query `m` with `O m`. -/
noncomputable def roIdealExperiment [Fintype M] [DecidableEq M] [Fintype T] [Nonempty T]
    [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (A : ROAdversary X Y M T) :
    ProbComp Bool := do
  let O ← ProbComp.uniform (M → T)
  let f ← ProbComp.uniform (X → Y)
  A.run (OracleComp.sumHandler (fun x => pure (f x)) (fun m => pure (O m)))

/-- The PRF distinguishing advantage of `A` against `F` in the random-oracle model
([BonehShoup2023], Attack Game 8.4). -/
noncomputable abbrev roAdvantage [Fintype M] [DecidableEq M] [Fintype T] [Nonempty T]
    [Fintype Key] [Nonempty Key] [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (F : (M → T) → Key → X → Y) (A : ROAdversary X Y M T) : ℝ≥0 :=
  Game.advantage (ProbComp.eval (roRealExperiment F A)) (ProbComp.eval (roIdealExperiment A))

/-- A budget on all queries is a budget on the random-oracle queries. -/
theorem ROAdversary.IsOracleQueryBounded.of_isQueryBounded {A : ROAdversary X Y M T} {Q : ℕ}
    (h : ProbOracleComp.IsQueryBounded A Q) : A.IsOracleQueryBounded Q :=
  OracleComp.IsCostBounded.of_le h fun q => by rcases q with _ | _ | _ <;> simp

/-- The key-prepending function `F_pre(k, x) = H (k ‖ x)` of a hash function `H`
([BonehShoup2023], Section 8.10.2), for a pairing `encode` of keys and inputs into hash inputs. -/
def prependKey (encode : Key → X → M) (H : M → T) (key : Key) (x : X) : T := H (encode key x)

/-- `prependKey encode H` evaluates `H` at the pairing of the key and the input. -/
@[simp] theorem prependKey_apply (encode : Key → X → M) (H : M → T) (key : Key) (x : X) :
    prependKey encode H key x = H (encode key x) := by unfold prependKey; rfl

/-! ### The challengers of the proof -/

section Tracking

variable {encode : Key → X → M}

/-- Memoryless answers of the challenger holding the table `f` for `F`-queries and the oracle `O`
for `O`-queries. -/
private noncomputable abbrev answers (f : X → Y) (O : M → T) :
    (q : X ⊕ M) → PMF (ROSpec X Y M T q) :=
  OracleComp.sumHandler (fun x => PMF.pure (f x)) (fun m => PMF.pure (O m))

/-- The law of a run against the challenger holding `f` and `O`. -/
private theorem eval_run_answers (f : X → Y) (O : M → T) {α : Type}
    (A : ProbOracleComp (ROSpec X Y M T) α) :
    ProbComp.eval (A.run (OracleComp.sumHandler (fun x => pure (f x)) (fun m => pure (O m)))) =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (answers f O)) A := by
  rw [ProbOracleComp.eval_run]
  have h : (fun q => ProbComp.eval
      (OracleComp.sumHandler (spec₁ := fun _ : X => Y) (spec₂ := fun _ : M => T)
        (fun x => pure (f x)) (fun m => pure (O m)) q)) = answers f O := by
    funext q
    cases q <;> simp [answers]
  rw [h]

/-- The key of an oracle point of the form `encode k x`, if it has this form. -/
private noncomputable def keyOf (encode : Key → X → M) (m : M) : Option Key :=
  open Classical in if h : ∃ k x, encode k x = m then some h.choose else none

private theorem keyOf_encode (hencode : Function.Injective2 encode) (k : Key) (x : X) :
    keyOf encode (encode k x) = some k := by
  rw [keyOf]
  split
  · next h =>
    obtain ⟨x', hx'⟩ := h.choose_spec
    exact congrArg some (hencode hx').1
  · next h => exact absurd ⟨k, x, rfl⟩ h

variable [DecidableEq Key]

/-- The keys named by the `O`-queries so far, after one more query. -/
private noncomputable def track (encode : Key → X → M) : X ⊕ M → Finset Key → Finset Key
  | .inl _, S => S
  | .inr m, S => (keyOf encode m).elim S (insert · S)

private theorem subset_track (q : X ⊕ M) (S : Finset Key) : S ⊆ track encode q S := by
  cases q with
  | inl x => exact subset_rfl
  | inr m =>
    rw [track]
    cases keyOf encode m with
    | none => exact subset_rfl
    | some k => exact Finset.subset_insert k S

private theorem card_track_le (q : X ⊕ M) (S : Finset Key) :
    (track encode q S).card ≤ S.card + Sum.elim (fun _ => 0) (fun _ => 1) q := by
  cases q with
  | inl x => exact le_rfl
  | inr m =>
    rw [track]
    cases keyOf encode m with
    | none => exact Nat.le_succ _
    | some k => exact Finset.card_insert_le k S

/-- The challenger of `answers` that also records the keys named by the `O`-queries. -/
private noncomputable def tracked (encode : Key → X → M) (f : X → T) (O : M → T) (q : X ⊕ M) :
    StateT (Finset Key) PMF (ROSpec X T M T q) :=
  fun S => (answers f O q).map (·, track encode q S)

private theorem tracked_apply (f : X → T) (O : M → T) (q : X ⊕ M) (S : Finset Key) :
    tracked encode f O q S = (answers f O q).map (·, track encode q S) := rfl

/-- Forgetting the recorded keys gives the run against the memoryless challenger. -/
private theorem runWith_tracked_map_fst (f : X → T) (O : M → T) {α : Type}
    (A : ProbOracleComp (ROSpec X T M T) α) (S : Finset Key) :
    (ProbOracleComp.runWith (tracked encode f O) A S).map Prod.fst =
      OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (answers f O)) A := by
  have h := ProbOracleComp.runWith_map_state (tracked encode f O)
    (fun q => StateT.lift (answers f O q)) (fun _ => ()) (fun q S => by
      rw [tracked_apply, PMF.map_comp]
      change _ = (answers f O q).bind fun a => PMF.pure (a, ())
      rw [← PMF.bind_pure_comp]
      rfl) A S
  rw [ProbOracleComp.runWith_lift] at h
  have h' := congrArg (PMF.map Prod.fst) h
  rw [PMF.map_comp, PMF.map_comp] at h'
  exact h'.trans (PMF.map_id _)

/-- The recorded keys of a run number at most the `O`-queries of the program. -/
private theorem card_le_of_mem_support_runWith_tracked (f : X → T) (O : M → T) {α : Type}
    {A : ProbOracleComp (ROSpec X T M T) α} {Q : ℕ}
    (hQ : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) A Q)
    {z : α × Finset Key} (hz : z ∈ (ProbOracleComp.runWith (tracked encode f O) A ∅).support) :
    z.2.card ≤ Q := by
  have h := OracleComp.IsCostBounded.measure_le hQ
    (OracleComp.sumHandler (fun n => StateT.lift (ProbComp.unifOracle n)) (tracked encode f O))
    Finset.card (fun q S res S' hres => ?_) (s := ∅) (s' := z.2) (result := z.1) hz
  · simpa using h
  · cases q with
    | inl n =>
      change (res, S') ∈ (StateT.lift (ProbComp.unifOracle n) S).support at hres
      simp only [StateT.lift, Probability.PMF.monad_bind_eq_bind,
        Probability.PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff,
        Prod.mk.injEq] at hres
      obtain ⟨_, _, -, rfl⟩ := hres
      simp
    | inr q =>
      change (res, S') ∈ ((answers f O q).map (·, track encode q S)).support at hres
      obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hres
      rw [← (Prod.mk.inj heq).2]
      exact card_track_le q S

/-- Until an `O`-query names the key, the challenger whose oracle is replaced on the points of
that key by the table `f` answers as the challenger with an independent oracle. -/
private theorem identicalUntilBad_tracked (hencode : Function.Injective2 encode) (key : Key)
    (f : X → T) (O : M → T) :
    ProbOracleComp.IdenticalUntilBad (tracked encode f (Function.extend (encode key) f O))
      (tracked encode f O) (fun S => key ∈ S) := by
  refine OracleComp.IdenticalUntilBad.probOracleComp ⟨fun q S _ a S' hS' => ?_,
    fun q S hS x hx => ?_, fun q S hS x hx => ?_⟩
  · cases q with
    | inl x => rfl
    | inr m =>
      by_cases hm : ∃ x, encode key x = m
      · obtain ⟨x, rfl⟩ := hm
        have hkey : key ∈ track encode (.inr (encode key x) : X ⊕ M) S := by
          rw [track, keyOf_encode hencode]
          exact Finset.mem_insert_self key S
        have hne : S' ≠ track encode (.inr (encode key x) : X ⊕ M) S := fun h => hS' (h ▸ hkey)
        rw [tracked_apply, tracked_apply]
        simp [answers, PMF.pure_map, PMF.pure_apply, hne]
      · rw [tracked_apply, tracked_apply]
        change (PMF.map _ (PMF.pure (Function.extend (encode key) f O m))) _ = _
        rw [Function.extend_apply' _ _ _ hm]
  · obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rw [← heq]
    exact subset_track q S hS
  · obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rw [← heq]
    exact subset_track q S hS

end Tracking

section Bound

variable {encode : Key → X → M} [Fintype Key]

/-- Averaged over the key, a run that does not depend on the key names it with probability at most
`Q / |Key|`. -/
private theorem sum_toOuterMeasure_mem_le [DecidableEq Key] (f : X → T) (O : M → T) {α : Type}
    {A : ProbOracleComp (ROSpec X T M T) α} {Q : ℕ}
    (hQ : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 1))) A Q)
    (c : ℝ≥0∞) :
    ∑ key : Key, c *
        (ProbOracleComp.runWith (tracked encode f O) A ∅).toOuterMeasure {z | key ∈ z.2} ≤
      Q * c := by
  set P := ProbOracleComp.runWith (tracked encode f O) A ∅ with hP
  calc ∑ key : Key, c * P.toOuterMeasure {z | key ∈ z.2}
      = ∑' z, ∑ key : Key, c * Set.indicator {z : α × Finset Key | key ∈ z.2} P z := by
        simp_rw [PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
        exact (Summable.tsum_finsetSum fun _ _ => CompleteLattice.summable).symm
    _ ≤ ∑' z, P z * (Q * c) := by
        refine tsum_le_tsum fun z => ?_
        have hsum : ∑ key : Key, c * Set.indicator {z : α × Finset Key | key ∈ z.2} P z =
            z.2.card * (c * P z) := by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, mul_ite, mul_zero]
          rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
        rw [hsum]
        by_cases hz : P z = 0
        · simp [hz]
        · have hcard : z.2.card ≤ Q :=
            card_le_of_mem_support_runWith_tracked f O hQ ((PMF.mem_support_iff _ _).mpr hz)
          calc (z.2.card : ℝ≥0∞) * (c * P z) ≤ Q * (c * P z) := by gcongr
            _ = P z * (Q * c) := by ring
    _ = Q * c := by rw [ENNReal.tsum_mul_right, P.tsum_coe, one_mul]

variable [Nonempty Key]

/-- For a fixed table and oracle, replacing the oracle on the points of a uniform key by the table
changes the adversary's output by at most `Q / |Key|`. -/
private theorem advantage_bind_extend_le (hencode : Function.Injective2 encode) (f : X → T)
    (O : M → T) {A : ROAdversary X T M T} {Q : ℕ} (hQ : A.IsOracleQueryBounded Q) :
    (Game.advantage
        ((uniformOfFintype Key).bind fun key =>
          OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
            (answers f (Function.extend (encode key) f O))) A)
        (OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (answers f O)) A) : ℝ) ≤
      Q / Fintype.card Key := by
  classical
  set G1 : Key → PMF Bool := fun key =>
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
      (answers f (Function.extend (encode key) f O))) A with hG1
  set G2 : PMF Bool :=
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (answers f O)) A with hG2
  set bad : Key → ℝ≥0∞ := fun key =>
    (ProbOracleComp.runWith (tracked encode f O) A ∅).toOuterMeasure {z | key ∈ z.2} with hbad
  have h1 (key : Key) : G1 key true ≤ G2 true + bad key := by
    have hub := identicalUntilBad_tracked hencode key f O
    have h := hub.bind_apply_le A ∅ (fun z => PMF.pure z.1) true
    rw [hub.bad_eq] at h
    change (PMF.map Prod.fst _) true ≤ (PMF.map Prod.fst _) true + _ at h
    rwa [runWith_tracked_map_fst, runWith_tracked_map_fst] at h
  have h2 (key : Key) : G2 true ≤ G1 key true + bad key := by
    have hub := (identicalUntilBad_tracked hencode key f O).symm
    have h := hub.bind_apply_le A ∅ (fun z => PMF.pure z.1) true
    change (PMF.map Prod.fst _) true ≤ (PMF.map Prod.fst _) true + _ at h
    rwa [runWith_tracked_map_fst, runWith_tracked_map_fst] at h
  set u := uniformOfFintype Key with hu
  have hsum : ∑' key, u key * bad key ≤ Q * (Fintype.card Key : ℝ≥0∞)⁻¹ := by
    rw [tsum_fintype]
    simp only [hu, Cslib.Probability.PMF.uniformOfFintype_apply]
    exact sum_toOuterMeasure_mem_le (encode := encode) f O hQ _
  have hB : (Q : ℝ≥0∞) * (Fintype.card Key : ℝ≥0∞)⁻¹ ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top Q)
      (ENNReal.inv_ne_top.mpr (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
  have hle1 : (u.bind G1) true ≤ G2 true + Q * (Fintype.card Key : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply]
    calc ∑' key, u key * G1 key true ≤ ∑' key, (u key * G2 true + u key * bad key) :=
          tsum_le_tsum fun key => by rw [← mul_add]; gcongr; exact h1 key
      _ = G2 true + ∑' key, u key * bad key := by
          rw [tsum_add, ENNReal.tsum_mul_right, u.tsum_coe, one_mul]
      _ ≤ G2 true + Q * (Fintype.card Key : ℝ≥0∞)⁻¹ := by gcongr
  have hle2 : G2 true ≤ (u.bind G1) true + Q * (Fintype.card Key : ℝ≥0∞)⁻¹ := by
    rw [PMF.bind_apply]
    calc G2 true = ∑' key, u key * G2 true := by
          rw [ENNReal.tsum_mul_right, u.tsum_coe, one_mul]
      _ ≤ ∑' key, (u key * G1 key true + u key * bad key) :=
          tsum_le_tsum fun key => by rw [← mul_add]; gcongr; exact h2 key
      _ = (∑' key, u key * G1 key true) + ∑' key, u key * bad key := tsum_add
      _ ≤ (∑' key, u key * G1 key true) + Q * (Fintype.card Key : ℝ≥0∞)⁻¹ := by gcongr
  have h := Game.advantage_le_of_apply_le hB hle1 hle2
  rwa [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, ENNReal.toReal_natCast,
    ← div_eq_mul_inv] at h

end Bound

/-! ### Theorem 8.9 -/

section Statements

variable [Fintype M] [DecidableEq M] [Fintype T] [Nonempty T] [Fintype Key] [Nonempty Key]

/-- The law of `roRealExperiment`: a uniform oracle table and a uniform key, then the adversary
interpreted at the `PMF` level. -/
theorem eval_roRealExperiment (F : (M → T) → Key → X → Y) (A : ROAdversary X Y M T) :
    ProbComp.eval (roRealExperiment F A) =
      (uniformOfFintype (M → T)).bind fun O => (uniformOfFintype Key).bind fun key =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (OracleComp.sumHandler (fun x => PMF.pure (F O key x)) fun m => PMF.pure (O m))) A := by
  simp only [roRealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, eval_run_answers]

variable [Fintype X] [DecidableEq X]

/-- The law of `roIdealExperiment`: a uniform oracle table and a uniform function, then the
adversary interpreted at the `PMF` level. -/
theorem eval_roIdealExperiment [Fintype Y] [Nonempty Y] (A : ROAdversary X Y M T) :
    ProbComp.eval (roIdealExperiment A) =
      (uniformOfFintype (M → T)).bind fun O => (uniformOfFintype (X → Y)).bind fun f =>
        OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle
          (OracleComp.sumHandler (fun x => PMF.pure (f x)) fun m => PMF.pure (O m))) A := by
  simp only [roIdealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform, eval_run_answers]

/-- A keyed function that ignores the oracle, against an adversary that does not query it:
Attack Game 8.4 is then Attack Game 4.2 ([BonehShoup2023]). -/
theorem roAdvantage_const_simulate [Fintype Y] [Nonempty Y] (F : Key → X → Y)
    (A : Adversary X Y) :
    roAdvantage (M := M) (T := T) (fun _ => F)
      (ProbOracleComp.simulate (fun x => ProbOracleComp.query (Sum.inl x)) A) = advantage F A := by
  have hreal : ProbComp.eval (roRealExperiment (M := M) (T := T) (fun _ => F)
      (ProbOracleComp.simulate (fun x => ProbOracleComp.query (Sum.inl x)) A)) =
      ProbComp.eval (realExperiment F A) := by
    simp only [roRealExperiment, realExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.run_simulate, ProbOracleComp.run_query]
    exact PMF.bind_const (uniformOfFintype (M → T))
      ((uniformOfFintype Key).bind fun key => (ProbOracleComp.run A fun x => pure (F key x)).eval)
  have hideal : ProbComp.eval (roIdealExperiment (M := M) (T := T)
      (ProbOracleComp.simulate (fun x => ProbOracleComp.query (Sum.inl x)) A)) =
      ProbComp.eval (idealExperiment A) := by
    simp only [roIdealExperiment, idealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform,
      ProbOracleComp.run_simulate, ProbOracleComp.run_query]
    exact PMF.bind_const (uniformOfFintype (M → T))
      ((uniformOfFintype (X → Y)).bind fun f => (ProbOracleComp.run A fun x => pure (f x)).eval)
  rw [roAdvantage, advantage, hreal, hideal]

/-- **Theorem 8.9, concrete bound** ([BonehShoup2023], Section 8.10.2, p. 329). If `encode` is
injective in the pair of its arguments, an adversary that makes at most `Q` random-oracle queries
distinguishes `F_pre(k, x) = O (encode k x)` from a random function with advantage at most
`Q / |Key|`. Nothing is assumed about its `F`-queries, its private coins or its running time. -/
theorem roAdvantage_prependKey_le {encode : Key → X → M} (hencode : Function.Injective2 encode)
    {A : ROAdversary X T M T} {Q : ℕ} (hQ : A.IsOracleQueryBounded Q) :
    (roAdvantage (prependKey encode) A : ℝ) ≤ Q / Fintype.card Key := by
  classical
  rw [roAdvantage, eval_roRealExperiment, eval_roIdealExperiment]
  set G : (X → T) → (M → T) → PMF Bool := fun f O =>
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifOracle (answers f O)) A with hG
  have hreal : ((uniformOfFintype (M → T)).bind fun O => (uniformOfFintype Key).bind fun key =>
      G (prependKey encode O key) O) =
      (uniformOfFintype (M → T)).bind fun O => (uniformOfFintype (X → T)).bind fun f =>
        (uniformOfFintype Key).bind fun key => G f (Function.extend (encode key) f O) := by
    calc _ = (uniformOfFintype Key).bind fun key => (uniformOfFintype (M → T)).bind fun O =>
          G (O ∘ encode key) O := PMF.bind_comm _ _ _
      _ = (uniformOfFintype Key).bind fun key => (uniformOfFintype (M → T)).bind fun O =>
          (uniformOfFintype (X → T)).bind fun f => G f (Function.extend (encode key) f O) := by
        congr 1
        funext key
        refine (Probability.PMF.uniformOfFintype_bind_bind_extend (encode key)
          fun O => G (O ∘ encode key) O).symm.trans ?_
        simp only [Function.extend_comp (hencode.right key)]
      _ = (uniformOfFintype (M → T)).bind fun O => (uniformOfFintype Key).bind fun key =>
          (uniformOfFintype (X → T)).bind fun f => G f (Function.extend (encode key) f O) :=
        PMF.bind_comm _ _ _
      _ = _ := by
        congr 1
        funext O
        exact PMF.bind_comm _ _ _
  rw [hreal]
  exact Game.advantage_bind_le _ _ _ fun O => Game.advantage_bind_le _ _ _ fun f =>
    advantage_bind_extend_le hencode f O hQ

end Statements

/-- **Theorem 8.9** ([BonehShoup2023], Section 8.10.2, p. 329). If `1 / |Key n|` is negligible,
the key-prepending function is a secure PRF in the random-oracle model in the following sense:
every family of adversaries whose number of random-oracle queries is polynomially bounded has
negligible advantage. The family need not be efficient; Definition 8.5 asks this only of efficient
adversaries. -/
theorem negligible_roAdvantage_prependKey {Key X M T : ℕ → Type}
    [∀ n, Fintype (M n)] [∀ n, DecidableEq (M n)] [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    [∀ n, Fintype (Key n)] [∀ n, Nonempty (Key n)] [∀ n, Fintype (X n)] [∀ n, DecidableEq (X n)]
    {encode : ∀ n, Key n → X n → M n} (hencode : ∀ n, Function.Injective2 (encode n))
    (hKey : Negligible fun n => (1 / Fintype.card (Key n) : ℝ≥0))
    {A : ∀ n, ROAdversary (X n) (T n) (M n) (T n)} {Q : ℕ → ℕ} (hQ : PolynomiallyBounded Q)
    (hA : ∀ n, (A n).IsOracleQueryBounded (Q n)) :
    Negligible fun n => roAdvantage (prependKey (encode n)) (A n) := by
  refine negligible_of_le (hKey.polynomiallyBounded_mul hQ) fun n => ?_
  rw [← NNReal.coe_le_coe]
  have h := roAdvantage_prependKey_le (hencode n) (hA n)
  simpa [div_eq_mul_inv] using h

/-! ### The book's bit strings -/

section BitStrings

open BitString

/-- The book's `k ‖ x` ([BonehShoup2023], Section 8.10.2): a `κ`-bit key followed by a word of
length at most `L`. -/
def keyAppend (κ L : ℕ) (k : BitString κ) (x : shortWords L) : shortWords (κ + L) :=
  ⟨List.ofFn k ++ x.1, mem_shortWords.mpr (by
    have := mem_shortWords.mp x.2
    simp only [List.length_append, List.length_ofFn]
    omega)⟩

/-- The word `keyAppend κ L k x` is the bits of `k` followed by the word `x`. -/
@[simp] theorem coe_keyAppend (κ L : ℕ) (k : BitString κ) (x : shortWords L) :
    (keyAppend κ L k x).1 = List.ofFn k ++ x.1 := by unfold keyAppend; rfl

/-- A key of fixed length followed by a word determines both. -/
theorem keyAppend_injective2 (κ L : ℕ) : Function.Injective2 (keyAppend κ L) := by
  intro k k' x x' h
  obtain ⟨hk, hx⟩ := List.append_inj (congrArg Subtype.val h) (by simp)
  exact ⟨List.ofFn_injective hk, Subtype.ext hx⟩

/-- **Theorem 8.9** ([BonehShoup2023], Section 8.10.2, p. 329) for `K = {0,1}^κ`,
`X = {0,1}^{≤L}` and `M = {0,1}^{≤κ+L}`: an adversary that makes at most `Q` random-oracle queries
has advantage at most `Q / 2 ^ κ`. -/
theorem roAdvantage_prependKey_keyAppend_le (κ L : ℕ) [Fintype T] [Nonempty T]
    {A : ROAdversary (shortWords L) T (shortWords (κ + L)) T} {Q : ℕ}
    (hQ : A.IsOracleQueryBounded Q) :
    (roAdvantage (prependKey (keyAppend κ L)) A : ℝ) ≤ Q / 2 ^ κ := by
  have h := roAdvantage_prependKey_le (keyAppend_injective2 κ L) hQ
  simpa [BitString] using h

/-- **Theorem 8.9** ([BonehShoup2023], Section 8.10.2, p. 329) for bit strings over a security
parameter: with keys of at least `n` bits at security parameter `n`, every family of adversaries
whose number of random-oracle queries is polynomially bounded has negligible advantage. -/
theorem negligible_roAdvantage_prependKey_keyAppend {κ : ℕ → ℕ} (hκ : ∀ n, n ≤ κ n) (L : ℕ → ℕ)
    {T : ℕ → Type} [∀ n, Fintype (T n)] [∀ n, Nonempty (T n)]
    {A : ∀ n, ROAdversary (shortWords (L n)) (T n) (shortWords (κ n + L n)) (T n)} {Q : ℕ → ℕ}
    (hQ : PolynomiallyBounded Q) (hA : ∀ n, (A n).IsOracleQueryBounded (Q n)) :
    Negligible fun n => roAdvantage (prependKey (keyAppend (κ n) (L n))) (A n) :=
  negligible_roAdvantage_prependKey (fun n => keyAppend_injective2 (κ n) (L n))
    (by simpa [BitString] using negligible_inv_two_pow_of_le hκ) hQ hA

end BitStrings

end Cslib.Crypto.PRF
