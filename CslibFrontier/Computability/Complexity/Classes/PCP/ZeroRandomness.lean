/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Classes.PCP
public import CslibFrontier.Computability.Complexity.Classes.PCP.NP
public import Mathlib.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# PCP without randomness

A PCP verifier (`Cslib.Complexity.PCPVerifier`) that uses no random bits reads the same positions
of the proof on every run, and soundness forces it to reject every proof of a non-member. The
classes with zero randomness are therefore classes of deterministic verification
[Arora and Barak, Chapter 11][AroraBarak09]:

* With no queries either, the verdict depends on the instance alone, so `PCP(0, 0) = P`
  (`Cslib.Complexity.PCP_zero_zero`). Since more randomness and more queries give larger classes,
  `P ⊆ PCP(r, q)` for all `r` and `q`.
* With `O(log n)` queries and no random bits, the verifier queries `O(log n)` input-determined
  positions; enumerating all `2 ^ O(log n)` bit tables for `PCPVerifier.tableVerifier` decides the
  problem in polynomial time, so `PCP(0, log n) = P` (`Cslib.Complexity.PCP_zero_log`, Arora and
  Barak, Chapter 18, Problem 4(i)).
* With polynomially many queries, the verifier can read a whole `NP` certificate, so
  `NP ⊆ PCP(0, poly)` (`Cslib.Complexity.exists_mem_PCP_zero_of_mem_NP`). Conversely, a
  verifier using no random bits uses at most logarithmically many, so `PCP(0, q) ⊆ NP` for every
  `q` (`Cslib.Complexity.PCP_log_subset_NP`), and `NP = PCP(0, poly)`
  (`Cslib.Complexity.mem_NP_iff_exists_PCP_zero`).

## Main definitions

* `Cslib.Complexity.PCPVerifier.exhaustiveTableDecider`: exhaustive check over all bit tables of
  length `(V.queryTable a).length`.

## Main results

* `Cslib.Complexity.PCP_zero_zero`: `PCP(0, 0) = P`.
* `Cslib.Complexity.P_subset_PCP`: `P ⊆ PCP(r, q)`.
* `Cslib.Complexity.PCPVerifier.isPolyTime_exhaustiveTableDecider`,
  `Cslib.Complexity.IsPCPVerifier.mem_iff_exhaustiveTableDecider`: polynomial-time exhaustive
  table search when `V.coins` and `(V.queryTable ·).length` are logarithmically bounded.
* `Cslib.Complexity.PCP_zero_log`: `PCP(0, log n) = P`.
* `Cslib.Complexity.exists_mem_PCP_zero_of_mem_NP`, `Cslib.Complexity.mem_NP_iff_exists_PCP_zero`:
  `NP = PCP(0, poly)`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Chapter 18, Problem §4(i)][AroraBarak07]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}


/-- **`PCP(0, 0) = P`**: a verifier with no random bits and no queries decides by its verdict on
the instance alone. -/
theorem PCP_zero_zero : PCP (fun _ => 0) (fun _ => 0) enc = P enc := by
  ext A
  constructor
  · rintro ⟨V, c, d, ⟨-, -, hv⟩, hcoins, hqs, hcomp, hsound⟩
    simp only [mul_zero, nonpos_iff_eq_zero] at hcoins hqs
    refine ⟨fun a => V.verdict ((a, []), []), ?_, fun a => ?_⟩
    · exact hv.comp (g := fun a : α => ((a, ([] : List Bool)), ([] : List Bool))) (by fun_prop)
    · -- with no random bits there are no queries, so the verdict ignores the proof
      have key (π : List Bool) : V.accepts a π [] = V.verdict ((a, []), []) := by
        grind [PCPVerifier.accepts, PCPVerifier.answers]
      constructor
      · intro ha
        obtain ⟨π, hπ⟩ := hcomp a ha
        change V.verdict ((a, []), []) = true
        rw [← key π]
        exact hπ [] (by simp [hcoins a])
      · intro hv'
        by_contra ha
        have := hsound a ha []
        rw [hcoins a, acceptCount_zero] at this
        simp [key, hv'] at this
  · rintro ⟨f, hf, hA⟩
    exact ⟨⟨fun _ => 0, fun _ => [], fun x => f x.1.1⟩, 0, 0,
      { coins := .const _
        queries := .const _
        verdict := hf.comp ((ComputableInPolyTime.fst enc encBits).comp
          (ComputableInPolyTime.fst (encPair enc encBits) encBits)) },
      { coins_le a := by simp
        length_queries_le a ρ _ := by simp
        complete a ha := ⟨[], fun ρ _ => by simpa [PCPVerifier.accepts] using (hA a).mp ha⟩
        sound a ha π := by
          have hfa : f a = false := by simpa [hA a] using ha
          rw [acceptCount_zero]
          simp [PCPVerifier.accepts, hfa] }⟩

/-- **`P ⊆ PCP(r, q)`** for all `r` and `q`. -/
theorem P_subset_PCP (r q : ℕ → ℕ) : P enc ⊆ PCP r q enc :=
  PCP_zero_zero (enc := enc) ▸
    (PCP_mono_randomness fun _ => Nat.zero_le _).trans (PCP_mono_queries fun _ => Nat.zero_le _)

namespace PCPVerifier

variable (V : PCPVerifier α)

/-- Exhaustively check whether any bit table of length `(V.queryTable a).length` makes
`V.tableVerifier` accept. -/
def exhaustiveTableDecider (a : α) : Bool :=
  (BitString.enumList (V.queryTable a).length).any fun table => V.tableVerifier (a, table)

variable {V}

/-- When a verifier uses zero random bits on `a`, its address table is the query list on `[]`. -/
theorem queryTable_of_coins_eq_zero {a : α} (hcoins : V.coins a = 0) :
    V.queryTable a = V.queries (a, []) := by
  simp [queryTable, hcoins]

/-- Exhaustive table search is polynomial-time whenever both `V.coins` and `(V.queryTable ·).length`
are logarithmically bounded. -/
theorem isPolyTime_exhaustiveTableDecider {c d : ℕ} (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1))
    (hqueries : ∀ a, (V.queryTable a).length ≤ d * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.exhaustiveTableDecider enc encBool := by
  have hlen : ComputableInPolyTime (fun a => (V.queryTable a).length) enc encUnary :=
    (ComputableInPolyTime.length_list encNat).comp (V.isPolyTime_queryTable hV hcoins)
  exact ComputableInPolyTime.anyWithInput (test := fun a table => V.tableVerifier (a, table))
    (isPolyTime_enumList_of_le_mul_log hlen hqueries) (V.isPolyTime_tableVerifier hV hcoins)

end PCPVerifier

/-- For any PCP verifier of `A`, an instance is in `A` if and only if `V.exhaustiveTableDecider`
accepts it. -/
theorem IsPCPVerifier.mem_iff_exhaustiveTableDecider {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (h : IsPCPVerifier enc r q V A) (a : α) :
    a ∈ A ↔ V.exhaustiveTableDecider a = true := by
  refine ⟨fun ha => ?_, fun hdec => ?_⟩
  · obtain ⟨proof, hproof⟩ := h.complete a ha
    refine List.any_eq_true.mpr ⟨PCPVerifier.answers proof (V.queryTable a), ?_, ?_⟩
    · rw [BitString.mem_enumList]
      simp [PCPVerifier.answers]
    · simpa using PCPVerifier.tableVerifier_complete a proof [] hproof
  · obtain ⟨table, _, htable⟩ := List.any_eq_true.mp hdec
    exact (h.mem_iff_exists_tableVerifier a).mpr ⟨table, htable⟩

/-- **`PCP(0, log n) = P` (Arora and Barak, Chapter 18, Problem 4(i)):** a verifier with no random
bits and logarithmically many queries reads `O(log n)` input-determined proof positions, so
enumerating all `2 ^ O(log n)` consistent bit tables decides the problem in polynomial time. -/
theorem PCP_zero_log : PCP (fun _ => 0) (fun n => Nat.log 2 n + 1) enc = P enc := by
  refine Set.Subset.antisymm ?_ (P_subset_PCP _ _)
  rintro A ⟨V, c, d, hV, hpcp⟩
  have hcoins0 (a : α) : V.coins a = 0 := by
    have := hpcp.coins_le a
    lia
  have hcoins (a : α) : V.coins a ≤ 0 * (Nat.log 2 (enc a).length + 1) := by
    simp [hcoins0 a]
  have hqueries (a : α) : (V.queryTable a).length ≤ d * (Nat.log 2 (enc a).length + 1) := by
    rw [PCPVerifier.queryTable_of_coins_eq_zero (hcoins0 a)]
    exact hpcp.length_queries_le a [] (by simp [hcoins0 a])
  exact ⟨V.exhaustiveTableDecider,
    V.isPolyTime_exhaustiveTableDecider hV hcoins hqueries,
    hpcp.mem_iff_exhaustiveTableDecider⟩

/-- **`NP ⊆ PCP(0, poly)`**: with no random bits, the verifier queries the first `p(n)` positions
of the proof, where `n` is the length of the encoded instance and `p(n)` the length of the
certificates, and runs the `NP` verifier on the bits read. -/
theorem exists_mem_PCP_zero_of_mem_NP {A : Set α} (hA : A ∈ NP enc) :
    ∃ k : ℕ, A ∈ PCP (fun _ => 0) (fun n => (n + 1) ^ k) enc := by
  obtain ⟨p, V, hV, hver⟩ := mem_NP.mp hA
  obtain ⟨c, k, hle⟩ := polynomiallyBounded_iff_le.mp (PolynomiallyBounded.polynomial_eval p)
  refine ⟨k, ⟨fun _ => 0, fun x => List.range (p.eval (enc x.1).length),
    fun y => V (y.1.1, y.2)⟩, 0, c,
    { coins := .const _
      queries := ?queries
      verdict := hV.comp (((ComputableInPolyTime.fst enc encBits).comp
        (ComputableInPolyTime.fst (encPair enc encBits) encBits)).pair
        (ComputableInPolyTime.snd (encPair enc encBits) encBits)) },
    { coins_le a := by simp
      length_queries_le a ρ _ := by simpa using hle (enc a).length
      complete := ?complete
      sound := ?sound }⟩
  case queries =>
    -- `x ↦ range (p (|enc x.1|))`, built in unary and converted elementwise to binary
    have h1 : ComputableInPolyTime (fun x : α × List Bool => p.eval (enc x.1).length)
        (encPair enc encBits) encUnary :=
      (ComputableInPolyTime.unary_eval p).comp
        ((ComputableInPolyTime.encoding_length enc).comp (ComputableInPolyTime.fst enc encBits))
    simpa [Function.comp_def] using
      (ComputableInPolyTime.map ComputableInPolyTime.unary_to_binary).comp
        (ComputableInPolyTime.range.comp h1)
  case complete =>
    intro a ha
    obtain ⟨w, hw, hVw⟩ := (hver a).mp ha
    refine ⟨w, fun ρ _ => ?_⟩
    simp only [PCPVerifier.accepts]
    rw [← hw, PCPVerifier.answers_range_length]
    exact hVw
  case sound =>
    intro a ha π
    have hrej : V (a, PCPVerifier.answers π (List.range (p.eval (enc a).length))) = false := by
      by_contra h
      exact ha ((hver a).mpr ⟨PCPVerifier.answers π (List.range (p.eval (enc a).length)),
        by simp [PCPVerifier.answers], Bool.not_eq_false _ ▸ h⟩)
    rw [acceptCount_zero]
    simp [PCPVerifier.accepts, hrej]

/-- **`NP = PCP(0, poly)`**: a problem is in `NP` exactly when it has a polynomial-time PCP
verifier using no random bits and polynomially many queries. -/
theorem mem_NP_iff_exists_PCP_zero {A : Set α} :
    A ∈ NP enc ↔ ∃ k : ℕ, A ∈ PCP (fun _ => 0) (fun n => (n + 1) ^ k) enc :=
  ⟨exists_mem_PCP_zero_of_mem_NP, fun ⟨_, hk⟩ =>
    (PCP_mono_randomness (fun _ => Nat.zero_le _)).trans (PCP_log_subset_NP _) hk⟩

end Cslib.Complexity
