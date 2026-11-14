/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PCP
public import CslibFrontier.Computability.Complexity.Classes.PCP.NP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Foundations.Data.BitString.List
public import CslibFrontier.Probability.BitString
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Computability.Complexity.Classes.SharpP.Probability
import CslibFrontier.Computability.PCP.Completeness
import CslibFrontier.Probability.BitString.List.All
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Robustness of the PCP class definition (Arora–Barak Chapter 18, Problems §1–§2)

`Cslib.Complexity.PCPWith c s r q enc` generalizes `Cslib.Complexity.PCP r q enc` to arbitrary
real completeness threshold `c` ("accept with probability `≥ c`") and soundness threshold `s`
("accept with probability `≤ s`"), leaving `PCP` definitionally unchanged and satisfying
`PCPWith 1 (1 / 2) r q enc = PCP r q enc` (`Cslib.Complexity.PCPWith_one_half`).

1. **Arbitrary soundness constant (`Cslib.Complexity.PCPWith_one`, Arora–Barak Ch. 18 Problem 1):**
   for all `r q : ℕ → ℕ` and every constant `0 < s < 1`,
   `PCPWith 1 s r q enc = PCP r q enc`.
   Independent `k`-fold repetition (`Cslib.Complexity.PCPVerifier.repeatAll`) multiplies the number
   of random bits and queries by `k` and raises the acceptance probability to the `k`-th power
   (`Cslib.Complexity.PCPVerifier.acceptProb_repeatAll`). Because a verifier's binary coin count
   `V.coins a` may exceed the length of a malformed random string `ρ` when `r` is superpolynomial,
   `PCPVerifier.repeatRowWidth` caps the per-round row width by `ρ.length`; on every valid random
   string of length `k * V.coins a` (`k ≥ 1`) this cap equals `V.coins a`.
2. **Imperfect completeness at logarithmic randomness and constant query complexity
   (`Cslib.Complexity.PCPWith_log_const`, Arora–Barak Ch. 18 Problem 2, corrected):**
   as printed in Arora and Barak ("completeness `c > 1 / 2` does not change `PCP(r, q)`" for all
   `r, q`), the claim would imply `BPP = coRP` at `q ≡ 0` and polynomial `r`. Under logarithmic
   randomness `r(n) = ⌊log₂ n⌋ + 1`, every completeness threshold `c > 1 / 2` and arbitrary query
   bound `q` lies in `NP` (`Cslib.Complexity.PCPWith_log_subset_NP`) by counting accepted random
   words on a first-occurrence query table (`PCPVerifier.tableAcceptCount`,
   `PCPVerifier.majorityTableVerifier`). Combining with the PCP theorem
   (`Cslib.Complexity.NP_eq_PCP_log`) gives
   `PCPWith c (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => q) enc =
     PCP (fun n => Nat.log 2 n + 1) (fun _ => q) enc`
   for every constant `q ≥ 1` and `1 / 2 < c ≤ 1`.

## Main definitions

* `Cslib.Complexity.PCPVerifier.acceptCount`, `Cslib.Complexity.PCPVerifier.acceptProb`:
  the number and fraction of random strings of length `V.coins a` on which `V` accepts `(a, π)`.
* `Cslib.Complexity.IsPCPVerifierWith`, `Cslib.Complexity.PCPWith`: PCP verifiers and complexity
  classes parameterized by completeness `c` and soundness `s`.
* `Cslib.Complexity.PCPVerifier.repeatRowWidth`, `Cslib.Complexity.PCPVerifier.repeatQueries`,
  `Cslib.Complexity.PCPVerifier.repeatAll`: polynomial-time `k`-fold independent repetition of a
  nonadaptive PCP verifier.
* `Cslib.Complexity.PCPVerifier.tableAcceptCount`,
  `Cslib.Complexity.PCPVerifier.majorityTableVerifier`: threshold table verification over all
  `2 ^ V.coins a` random strings.

## Main results

* `Cslib.Complexity.PCPVerifier.getD_answers_idxOf`: first-occurrence lookup in
  `answers π addresses` recovers `π.getD addr false`.
* `Cslib.Complexity.isPCPVerifierWith_one_half_iff`, `Cslib.Complexity.PCPWith_one_half`:
  `PCPWith 1 (1 / 2) r q enc = PCP r q enc`.
* `Cslib.Complexity.PCPVerifier.polyTime_repeatAll`,
  `Cslib.Complexity.PCPVerifier.acceptProb_repeatAll`,
  `Cslib.Complexity.IsPCPVerifierWith.repeatAll`, `Cslib.Complexity.PCPWith_subset_repeatAll`:
  `k`-fold repetition preserves polynomial time and raises completeness and soundness to the
  `k`-th power.
* `Cslib.Complexity.PCPWith_one`: `PCPWith 1 s r q enc = PCP r q enc` for `0 < s < 1`
  (**Arora–Barak Ch. 18 Problem 1**).
* `Cslib.Complexity.PCPVerifier.isPolyTime_majorityTableVerifier`,
  `Cslib.Complexity.IsPCPVerifierWith.mem_iff_exists_majorityTableVerifier`,
  `Cslib.Complexity.PCPWith_log_subset_NP`: logarithmic-randomness PCP with completeness `c > 1 / 2`
  and soundness `1 / 2` is contained in `NP`.
* `Cslib.Complexity.PCP_log_const`, `Cslib.Complexity.PCPWith_log_const`:
  `PCPWith c (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => q) enc =
    PCP (fun n => Nat.log 2 n + 1) (fun _ => q) enc` for `1 / 2 < c ≤ 1` and `1 ≤ q`
  (**Arora–Barak Ch. 18 Problem 2, corrected**).

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach* (2007 draft),
  Chapter 18, Problems §1, §2][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Cslib.Probability

variable {α : Type} {enc : α ↪ List Bool}

namespace PCPVerifier

variable (V : PCPVerifier α)

/-- Looking up the first occurrence of a queried address in `answers π addresses` recovers the bit
of `π` at that address. -/
theorem getD_answers_idxOf (π : List Bool) {addresses : List ℕ} {addr : ℕ}
    (haddr : addr ∈ addresses) :
    (answers π addresses).getD (addresses.idxOf addr) false = π.getD addr false := by
  simp [answers, List.getD_eq_getElem?_getD, List.idxOf_lt_length_iff.mpr haddr]

/-- The number of random strings of length `V.coins a` on which `V` accepts `(a, π)`. -/
def acceptCount (a : α) (π : List Bool) : ℕ :=
  Cslib.Complexity.acceptCount (fun x => V.accepts x.1 π x.2) a (V.coins a)

/-- The acceptance probability of `V` on instance `a` and proof `π` over a uniform random string of
length `V.coins a`. -/
noncomputable def acceptProb (a : α) (π : List Bool) : ℝ :=
  (V.acceptCount a π : ℝ) / 2 ^ V.coins a

theorem acceptCount_le_two_pow (a : α) (π : List Bool) :
    V.acceptCount a π ≤ 2 ^ V.coins a :=
  Cslib.Complexity.acceptCount_le_two_pow

theorem acceptProb_nonneg (a : α) (π : List Bool) : 0 ≤ V.acceptProb a π := by
  unfold acceptProb
  positivity

theorem acceptProb_le_one (a : α) (π : List Bool) : V.acceptProb a π ≤ 1 := by
  rw [acceptProb, div_le_iff₀ (by positivity), one_mul]
  exact_mod_cast V.acceptCount_le_two_pow a π

/-- `V.acceptProb a π` is the real probability that `V.accepts a π` returns `true` under
`BitString.uniformList (V.coins a)`. -/
theorem acceptProb_eq_uniformList_toReal (a : α) (π : List Bool) :
    V.acceptProb a π =
      (((BitString.uniformList (V.coins a)).map (fun ρ => V.accepts a π ρ)) true).toReal :=
  (uniformList_acceptCount_toReal (fun x => V.accepts x.1 π x.2) a (V.coins a)).symm

/-- Every random string of length `V.coins a` is accepted if and only if `V.acceptCount a π`
equals `2 ^ V.coins a`. -/
theorem acceptCount_eq_two_pow_iff (a : α) (π : List Bool) :
    V.acceptCount a π = 2 ^ V.coins a ↔
      ∀ ρ : List Bool, ρ.length = V.coins a → V.accepts a π ρ = true := by
  unfold acceptCount Cslib.Complexity.acceptCount
  rw [← BitString.countP_enumList (V.coins a) (fun ρ => V.accepts a π ρ),
    ← BitString.length_enumList (V.coins a), List.countP_eq_length]
  simp only [BitString.mem_enumList]

/-- Acceptance probability at least `1` is equivalent to accepting every random string of length
`V.coins a`. -/
theorem one_le_acceptProb_iff (a : α) (π : List Bool) :
    1 ≤ V.acceptProb a π ↔
      ∀ ρ : List Bool, ρ.length = V.coins a → V.accepts a π ρ = true := by
  rw [← V.acceptCount_eq_two_pow_iff a π, acceptProb, le_div_iff₀ (by positivity), one_mul]
  have hle := V.acceptCount_le_two_pow a π
  have hcast : (2 : ℝ) ^ V.coins a ≤ V.acceptCount a π ↔
      2 ^ V.coins a ≤ V.acceptCount a π := by norm_cast
  rw [hcast]
  omega

/-- Acceptance probability at most `1 / 2` is equivalent to `2 * V.acceptCount a π ≤ 2 ^ V.coins a`.
-/
theorem acceptProb_le_half_iff (a : α) (π : List Bool) :
    V.acceptProb a π ≤ 1 / 2 ↔ 2 * V.acceptCount a π ≤ 2 ^ V.coins a := by
  rw [V.acceptProb_eq_uniformList_toReal]
  exact (Cslib.Complexity.acceptCount_le_half_iff
    (fun x => V.accepts x.1 π x.2) a (V.coins a)).symm

end PCPVerifier

/-- `V` is a verifier for `A` with completeness `c ∈ ℝ` and soundness `s ∈ ℝ`, using at most
`r n` random bits and at most `q n` queries on instances whose encoding has length `n`:
every member of `A` has a proof accepted with probability at least `c`, and for every non-member,
every proof is accepted with probability at most `s` over a uniform random string of length
`V.coins a`. -/
structure IsPCPVerifierWith (enc : α ↪ List Bool) (c s : ℝ) (r q : ℕ → ℕ)
    (V : PCPVerifier α) (A : Set α) : Prop where
  /-- At most `r n` random bits on an instance whose encoding has length `n`. -/
  coins_le : ∀ a, V.coins a ≤ r (enc a).length
  /-- At most `q n` queries on an instance whose encoding has length `n`. -/
  length_queries_le :
    ∀ a (ρ : List Bool), ρ.length = V.coins a → (V.queries (a, ρ)).length ≤ q (enc a).length
  /-- Completeness: every member of `A` has a proof accepted with probability at least `c`. -/
  complete : ∀ a ∈ A, ∃ π : List Bool, c ≤ V.acceptProb a π
  /-- Soundness: on a non-member, every proof is accepted with probability at most `s`. -/
  sound : ∀ a ∉ A, ∀ π : List Bool, V.acceptProb a π ≤ s

/-- The class `PCP_{c, s}(r, q)` with respect to the encoding `enc` of instances: the problems with
a polynomial-time verifier with completeness `c` and soundness `s` using `O(r n)` random bits and
`O(q n)` queries on instances whose encoding has length `n`
[Arora and Barak, Chapter 18, Problems §1–§2][AroraBarak07]. -/
def PCPWith (c s : ℝ) (r q : ℕ → ℕ) (enc : α ↪ List Bool) : Set (Set α) :=
  {A | ∃ (V : PCPVerifier α) (c_r c_q : ℕ), V.PolyTime enc ∧
    IsPCPVerifierWith enc c s (fun n => c_r * r n) (fun n => c_q * q n) V A}

theorem mem_PCPWith {c s : ℝ} {r q : ℕ → ℕ} {A : Set α} :
    A ∈ PCPWith c s r q enc ↔
      ∃ (V : PCPVerifier α) (c_r c_q : ℕ), V.PolyTime enc ∧
        IsPCPVerifierWith enc c s (fun n => c_r * r n) (fun n => c_q * q n) V A :=
  Iff.rfl

/-- At completeness `1` and soundness `1 / 2`, `IsPCPVerifierWith` is equivalent to
`IsPCPVerifier`. -/
theorem isPCPVerifierWith_one_half_iff {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α} :
    IsPCPVerifierWith enc 1 (1 / 2) r q V A ↔ IsPCPVerifier enc r q V A := by
  constructor
  · rintro ⟨hcoins, hq, hcomp, hsound⟩
    refine ⟨hcoins, hq, fun a ha => ?_, fun a ha π => ?_⟩
    · obtain ⟨π, hπ⟩ := hcomp a ha
      exact ⟨π, (V.one_le_acceptProb_iff a π).mp hπ⟩
    · exact (V.acceptProb_le_half_iff a π).mp (hsound a ha π)
  · rintro ⟨hcoins, hq, hcomp, hsound⟩
    refine ⟨hcoins, hq, fun a ha => ?_, fun a ha π => ?_⟩
    · obtain ⟨π, hπ⟩ := hcomp a ha
      exact ⟨π, (V.one_le_acceptProb_iff a π).mpr hπ⟩
    · exact (V.acceptProb_le_half_iff a π).mpr (hsound a ha π)

/-- `PCPWith 1 (1 / 2) r q enc` coincides with `PCP r q enc`. -/
theorem PCPWith_one_half (r q : ℕ → ℕ) : PCPWith 1 (1 / 2) r q enc = PCP r q enc := by
  ext A
  simp only [mem_PCPWith, mem_PCP, isPCPVerifierWith_one_half_iff]

theorem IsPCPVerifierWith.mono_randomness {c s : ℝ} {r r' q : ℕ → ℕ} {V : PCPVerifier α}
    {A : Set α} (hr : ∀ n, r n ≤ r' n) (h : IsPCPVerifierWith enc c s r q V A) :
    IsPCPVerifierWith enc c s r' q V A :=
  { h with coins_le a := (h.coins_le a).trans (hr _) }

theorem IsPCPVerifierWith.mono_queries {c s : ℝ} {r q q' : ℕ → ℕ} {V : PCPVerifier α}
    {A : Set α} (hq : ∀ n, q n ≤ q' n) (h : IsPCPVerifierWith enc c s r q V A) :
    IsPCPVerifierWith enc c s r q' V A :=
  { h with length_queries_le a ρ hρ := (h.length_queries_le a ρ hρ).trans (hq _) }

theorem IsPCPVerifierWith.mono_thresholds {c c' s s' : ℝ} {r q : ℕ → ℕ} {V : PCPVerifier α}
    {A : Set α} (hc : c' ≤ c) (hs : s ≤ s') (h : IsPCPVerifierWith enc c s r q V A) :
    IsPCPVerifierWith enc c' s' r q V A :=
  { h with
    complete a ha := let ⟨π, hπ⟩ := h.complete a ha; ⟨π, hc.trans hπ⟩
    sound a ha π := (h.sound a ha π).trans hs }

/-- Lowering completeness or raising soundness gives a larger class. -/
theorem PCPWith_mono_thresholds {c c' s s' : ℝ} {r q : ℕ → ℕ} (hc : c' ≤ c) (hs : s ≤ s') :
    PCPWith c s r q enc ⊆ PCPWith c' s' r q enc :=
  fun _ ⟨V, c_r, c_q, hV, h⟩ => ⟨V, c_r, c_q, hV, h.mono_thresholds hc hs⟩

/-- More randomness gives a larger `PCPWith` class. -/
theorem PCPWith_mono_randomness {c s : ℝ} {r r' q : ℕ → ℕ} (hr : ∀ n, r n ≤ r' n) :
    PCPWith c s r q enc ⊆ PCPWith c s r' q enc :=
  fun _ ⟨V, c_r, c_q, hV, h⟩ =>
    ⟨V, c_r, c_q, hV, h.mono_randomness fun n => Nat.mul_le_mul_left c_r (hr n)⟩

/-- More queries give a larger `PCPWith` class. -/
theorem PCPWith_mono_queries {c s : ℝ} {r q q' : ℕ → ℕ} (hq : ∀ n, q n ≤ q' n) :
    PCPWith c s r q enc ⊆ PCPWith c s r q' enc :=
  fun _ ⟨V, c_r, c_q, hV, h⟩ =>
    ⟨V, c_r, c_q, hV, h.mono_queries fun n => Nat.mul_le_mul_left c_q (hq n)⟩

/-! ### Independent repetition and Arora–Barak Chapter 18, Problem 1 -/

namespace PCPVerifier

variable (V : PCPVerifier α)

/-- The per-round coin width on `(a, ρ)`, capped by `ρ.length` so that malformed short random
strings never pad beyond the input length. On any valid random string of length `k * V.coins a`
(`k ≥ 1`), this equals `V.coins a`. -/
def repeatRowWidth (a : α) (ρ : List Bool) : ℕ :=
  min ρ.length (V.coins a)

/-- All proof addresses queried across `k` independent rounds on `(a, ρ)`. -/
def repeatQueries (k : ℕ) (p : α × List Bool) : List ℕ :=
  let w := V.repeatRowWidth p.1 p.2
  (List.range k).flatMap fun i => V.queries (p.1, BitString.listRow w i p.2)

/-- Independent `k`-fold repetition of a nonadaptive PCP verifier `V`: runs `k` independent trials
using disjoint coin blocks of width `V.coins a` and accepts when all `k` trials accept. Repeated
proof queries across or within trials are resolved consistently via first-occurrence lookup in
`V.repeatQueries k`. -/
def repeatAll (k : ℕ) : PCPVerifier α where
  coins a := k * V.coins a
  queries := V.repeatQueries k
  verdict
  | ((a, ρ), ans) =>
    let w := V.repeatRowWidth a ρ
    let allQueries := V.repeatQueries k (a, ρ)
    (List.range k).all fun i =>
      let ρ_i := BitString.listRow w i ρ
      V.verdict ((a, ρ_i), (V.queries (a, ρ_i)).map fun addr =>
        ans.getD (allQueries.idxOf addr) false)

@[simp]
theorem coins_repeatAll (k : ℕ) (a : α) : (V.repeatAll k).coins a = k * V.coins a := rfl

@[simp]
theorem queries_repeatAll (k : ℕ) (p : α × List Bool) :
    (V.repeatAll k).queries p = V.repeatQueries k p := rfl

theorem repeatRowWidth_of_le {a : α} {ρ : List Bool} (h : V.coins a ≤ ρ.length) :
    V.repeatRowWidth a ρ = V.coins a :=
  Nat.min_eq_right h

theorem mem_repeatQueries {k i : ℕ} {a : α} {ρ : List Bool} {addr : ℕ}
    (hi : i ∈ List.range k)
    (haddr : addr ∈ V.queries (a, BitString.listRow (V.repeatRowWidth a ρ) i ρ)) :
    addr ∈ V.repeatQueries k (a, ρ) :=
  List.mem_flatMap.mpr ⟨i, hi, haddr⟩

/-- If each valid single-round query list has length at most `B`, then `k` repetitions on a random
string of length `k * V.coins a` make at most `k * B` queries. -/
theorem length_queries_repeatAll_le (k : ℕ) {a : α} {ρ : List Bool} {B : ℕ}
    (hρ : ρ.length = (V.repeatAll k).coins a)
    (hq : ∀ word : List Bool, word.length = V.coins a → (V.queries (a, word)).length ≤ B) :
    ((V.repeatAll k).queries (a, ρ)).length ≤ k * B := by
  cases k with
  | zero =>
    clear hq
    simp [repeatAll, repeatQueries]
  | succ k =>
    have hle : V.coins a ≤ ρ.length := by
      rw [hρ, coins_repeatAll]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    rw [queries_repeatAll, repeatQueries]
    dsimp only
    rw [V.repeatRowWidth_of_le hle, List.length_flatMap]
    have hbound : ∀ i ∈ List.range (k + 1),
        (V.queries (a, BitString.listRow (V.coins a) i ρ)).length ≤ B :=
      fun i _ => hq _ (BitString.length_listRow (V.coins a) i ρ)
    simpa [List.length_range, smul_eq_mul] using
      List.sum_le_length_nsmul ((List.range (k + 1)).map
        fun i => (V.queries (a, BitString.listRow (V.coins a) i ρ)).length) B
        (by
          intro x hx
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
          exact hbound i hi)

/-- First-occurrence lookup in `V.repeatQueries k` recovers each trial's individual verdict. -/
theorem accepts_repeatAll_eq (k : ℕ) (a : α) (π ρ : List Bool) :
    (V.repeatAll k).accepts a π ρ =
      (List.range k).all fun i =>
        V.accepts a π (BitString.listRow (V.repeatRowWidth a ρ) i ρ) := by
  apply Bool.eq_iff_iff.mpr
  simp only [PCPVerifier.accepts, repeatAll, List.all_eq_true]
  refine forall_congr' fun i => forall_congr' fun hi => ?_
  apply Iff.of_eq
  congr 3
  unfold answers
  refine List.map_congr_left fun addr haddr => ?_
  exact getD_answers_idxOf π (V.mem_repeatQueries hi haddr)

/-- On any random string of length `k * V.coins a`, `V.repeatAll k` accepts iff every coin block
of width `V.coins a` accepts. -/
theorem accepts_repeatAll (k : ℕ) (a : α) (π ρ : List Bool)
    (hρ : ρ.length = (V.repeatAll k).coins a) :
    (V.repeatAll k).accepts a π ρ =
      (List.range k).all fun i => V.accepts a π (BitString.listRow (V.coins a) i ρ) := by
  rw [V.accepts_repeatAll_eq]
  cases k with
  | zero => rfl
  | succ k =>
    have hle : V.coins a ≤ ρ.length := by
      rw [hρ, coins_repeatAll]
      exact Nat.le_mul_of_pos_left _ (Nat.succ_pos k)
    rw [V.repeatRowWidth_of_le hle]

/-- Independent `k`-fold repetition raises the acceptance probability to the `k`-th power. -/
theorem acceptProb_repeatAll (k : ℕ) (a : α) (π : List Bool) :
    (V.repeatAll k).acceptProb a π = V.acceptProb a π ^ k := by
  rw [acceptProb_eq_uniformList_toReal, acceptProb_eq_uniformList_toReal,
    coins_repeatAll, ← ENNReal.toReal_pow,
    ← BitString.uniformList_all_listRow_true k (V.coins a) (fun ρ => V.accepts a π ρ)]
  congr 2
  refine PMF.map_congr_on_support _ _ _ fun ρ hρ => ?_
  rw [BitString.mem_support_uniformList_iff] at hρ
  exact V.accepts_repeatAll k a π ρ hρ

variable {V}

/-- `V.repeatAll k` is polynomial-time whenever `V` is. -/
theorem polyTime_repeatAll (hV : V.PolyTime enc) (k : ℕ) :
    (V.repeatAll k).PolyTime enc := by
  have hwidth : ComputableInPolyTime (fun p : α × List Bool => V.repeatRowWidth p.1 p.2)
      (encPair enc encBits) encUnary :=
    (ComputableInPolyTime.length_bits.comp
      (ComputableInPolyTime.snd enc encBits)).binary_min_unary'
      (hV.coins.comp (ComputableInPolyTime.fst enc encBits))
  have hqueries : ComputableInPolyTime (V.repeatQueries k)
      (encPair enc encBits) (encList encNat) := by
    have hp := ComputableInPolyTime.fst (encPair enc encBits) encUnary
    have hi := ComputableInPolyTime.snd (encPair enc encBits) encUnary
    have hrow := ComputableInPolyTime.bitsRowWithInput (hwidth.comp hp) hi hp.snd'
    unfold repeatQueries
    exact ComputableInPolyTime.flatMapWithInput
      (.const (encOut := encList encUnary) (List.range k))
      (hV.queries.comp (hp.fst'.prod hrow))
  refine { coins := ?_, queries := hqueries, verdict := ?_ }
  · exact (ComputableInPolyTime.const k).binary_mul' hV.coins
  · have hp := ComputableInPolyTime.fst (encPair (encPair enc encBits) encBits) encUnary
    have hi := ComputableInPolyTime.snd (encPair (encPair enc encBits) encBits) encUnary
    have ha := hp.fst'.fst'
    have hρ := hp.fst'.snd'
    have hans := hp.snd'
    have hrow := ComputableInPolyTime.bitsRowWithInput (hwidth.comp hp.fst') hi hρ
    have hqi := hV.queries.comp (ha.prod hrow)
    have hallQ := hqueries.comp hp.fst'
    have hx := ComputableInPolyTime.fst
      (encPair (encPair (encPair enc encBits) encBits) encUnary) encNat
    have haddr := ComputableInPolyTime.snd
      (encPair (encPair (encPair enc encBits) encBits) encUnary) encNat
    have hlookup := (ComputableInPolyTime.bitsGetD false).comp
      ((hans.comp hx).prod ((ComputableInPolyTime.idxOf encNat).comp ((hallQ.comp hx).prod haddr)))
    have hmap := ComputableInPolyTime.mapToBitsWithInput
      (f := fun (x : ((α × List Bool) × List Bool) × ℕ) (addr : ℕ) =>
        x.1.2.getD ((V.repeatQueries k x.1.1).idxOf addr) false)
      hqi hlookup
    simpa only [repeatAll] using ComputableInPolyTime.allWithInput
      (test := fun (p : (α × List Bool) × List Bool) (i : ℕ) =>
        V.verdict ((p.1.1, BitString.listRow (V.repeatRowWidth p.1.1 p.1.2) i p.1.2),
          (V.queries (p.1.1, BitString.listRow (V.repeatRowWidth p.1.1 p.1.2) i p.1.2)).map
            fun addr => p.2.getD ((V.repeatQueries k p.1).idxOf addr) false))
      (.const (encOut := encList encUnary) (List.range k))
      (hV.verdict.comp ((ha.prod hrow).prod hmap))

end PCPVerifier

/-- Independent `k`-fold repetition transforms a `(c, s)`-verifier with bounds `(r, q)` into a
`(c ^ k, s ^ k)`-verifier with bounds `(k * r, k * q)`. -/
theorem IsPCPVerifierWith.repeatAll {c s : ℝ} {r q : ℕ → ℕ} {V : PCPVerifier α} {A : Set α}
    (hc : 0 ≤ c) (h : IsPCPVerifierWith enc c s r q V A) (k : ℕ) :
    IsPCPVerifierWith enc (c ^ k) (s ^ k) (fun n => k * r n) (fun n => k * q n)
      (V.repeatAll k) A where
  coins_le a := Nat.mul_le_mul_left k (h.coins_le a)
  length_queries_le a ρ hρ :=
    V.length_queries_repeatAll_le k hρ (h.length_queries_le a)
  complete a ha := by
    obtain ⟨π, hπ⟩ := h.complete a ha
    refine ⟨π, ?_⟩
    rw [V.acceptProb_repeatAll]
    exact pow_le_pow_left₀ hc hπ k
  sound a ha π := by
    rw [V.acceptProb_repeatAll]
    exact pow_le_pow_left₀ (V.acceptProb_nonneg a π) (h.sound a ha π) k

/-- Independent `k`-fold repetition maps `PCPWith c s r q enc` into
`PCPWith (c ^ k) (s ^ k) r q enc`. -/
theorem PCPWith_subset_repeatAll {c s : ℝ} {r q : ℕ → ℕ} (hc : 0 ≤ c) (k : ℕ) :
    PCPWith c s r q enc ⊆ PCPWith (c ^ k) (s ^ k) r q enc := by
  rintro A ⟨V, c_r, c_q, hV, hpcp⟩
  refine ⟨V.repeatAll k, k * c_r, k * c_q, V.polyTime_repeatAll hV k, ?_⟩
  simpa only [Nat.mul_assoc] using hpcp.repeatAll hc k

/-- Any soundness constant `s < 1` can be amplified below any positive soundness target `0 < s'` by
constant-fold repetition. -/
theorem PCPWith_one_subset_of_lt_one {s s' : ℝ} {r q : ℕ → ℕ} (hs1 : s < 1) (hs' : 0 < s') :
    PCPWith 1 s r q enc ⊆ PCPWith 1 s' r q enc := by
  rcases le_or_gt 0 s with hs0 | hs_neg
  · obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one hs' hs1
    refine (PCPWith_subset_repeatAll zero_le_one k).trans ?_
    simpa only [one_pow] using PCPWith_mono_thresholds le_rfl hk.le
  · exact PCPWith_mono_thresholds le_rfl (hs_neg.le.trans hs'.le)

/-- **Arora and Barak, Chapter 18, Problem 1:** for all `r q : ℕ → ℕ` and every soundness constant
`0 < s < 1`, `PCPWith 1 s r q enc = PCP r q enc`. -/
theorem PCPWith_one {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (r q : ℕ → ℕ) :
    PCPWith 1 s r q enc = PCP r q enc := by
  rw [← PCPWith_one_half]
  exact Set.Subset.antisymm
    (PCPWith_one_subset_of_lt_one hs1 (by norm_num))
    (PCPWith_one_subset_of_lt_one (by norm_num) hs0)

/-! ### Threshold table verification and Arora–Barak Chapter 18, Problem 2 (corrected) -/

namespace PCPVerifier

variable (V : PCPVerifier α)

/-- Number of random words of length `V.coins input.1` on which `V` accepts using the bit at each
queried address's first occurrence in `V.queryTable input.1`. -/
def tableAcceptCount (input : α × List Bool) : ℕ :=
  let addresses := V.queryTable input.1
  (BitString.enumList (V.coins input.1)).countP fun word =>
    V.verdict ((input.1, word), (V.queries (input.1, word)).map fun address =>
      input.2.getD (addresses.idxOf address) false)

/-- A genuine proof supplies a table whose accepted-word count is `V.acceptCount a proof`;
trailing padding is ignored. -/
theorem tableAcceptCount_answers_append (a : α) (proof padding : List Bool) :
    V.tableAcceptCount (a, answers proof (V.queryTable a) ++ padding) =
      V.acceptCount a proof := by
  unfold tableAcceptCount acceptCount Cslib.Complexity.acceptCount
  rw [← BitString.countP_enumList (V.coins a) (fun word => V.accepts a proof word)]
  refine List.countP_congr fun word hword => ?_
  rw [V.verdict_answers_queryTable_append a proof padding word (BitString.mem_enumList.mp hword)]

/-- Every bit table has the exact same accepted-word count as its expanded proof
`V.proofOfTable a table`. -/
theorem tableAcceptCount_eq_acceptCount_proofOfTable (a : α) (table : List Bool) :
    V.tableAcceptCount (a, table) = V.acceptCount a (V.proofOfTable a table) := by
  unfold tableAcceptCount acceptCount Cslib.Complexity.acceptCount
  rw [← BitString.countP_enumList (V.coins a)
    (fun word => V.accepts a (V.proofOfTable a table) word)]
  refine List.countP_congr fun word hword => ?_
  rw [V.accepts_proofOfTable a table word (BitString.mem_enumList.mp hword)]

/-- Exhaustively check whether strictly more than half of the random words of length
`V.coins input.1` accept using the bit at each address's first table occurrence. -/
def majorityTableVerifier (input : α × List Bool) : Bool :=
  decide ((BitString.enumList (V.coins input.1)).length < 2 * V.tableAcceptCount input)

/-- A proof with acceptance probability strictly above `1 / 2` makes `V.majorityTableVerifier`
accept its query table with arbitrary trailing padding. -/
theorem majorityTableVerifier_complete (a : α) (proof padding : List Bool)
    (h : 1 / 2 < V.acceptProb a proof) :
    V.majorityTableVerifier (a, answers proof (V.queryTable a) ++ padding) = true := by
  simp only [majorityTableVerifier, BitString.length_enumList, decide_eq_true_eq,
    V.tableAcceptCount_answers_append]
  have hnot : ¬ V.acceptProb a proof ≤ 1 / 2 := not_le.mpr h
  rwa [V.acceptProb_le_half_iff, not_le] at hnot

variable {V} {c : ℕ}

/-- Counting accepted random words on a table is polynomial-time under a logarithmic coin bound. -/
theorem isPolyTime_tableAcceptCount (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.tableAcceptCount (encPair enc encBits) encUnary :=
  ComputableInPolyTime.countPWithInput
    ((V.isPolyTime_enumCoins hV hcoins).comp (ComputableInPolyTime.fst enc encBits))
    (V.isPolyTime_tableWordVerdict hV hcoins)

/-- Majority table verification is polynomial-time under a logarithmic coin bound. -/
theorem isPolyTime_majorityTableVerifier (hV : V.PolyTime enc)
    (hcoins : ∀ a, V.coins a ≤ c * (Nat.log 2 (enc a).length + 1)) :
    ComputableInPolyTime V.majorityTableVerifier (encPair enc encBits) encBool := by
  have he := V.isPolyTime_enumCoins hV hcoins
  have htotal : ComputableInPolyTime
      (fun input : α × List Bool => (BitString.enumList (V.coins input.1)).length)
      (encPair enc encBits) encUnary :=
    (ComputableInPolyTime.length_list encBits).comp
      (he.comp (ComputableInPolyTime.fst enc encBits))
  have hcount := V.isPolyTime_tableAcceptCount hV hcoins
  have htwo : ComputableInPolyTime (fun _ : α × List Bool => 2) (encPair enc encBits) encUnary :=
    .const 2
  exact .of_tidy (htotal.tidy.unary_lt' (htwo.unary_mul' hcount).tidy)

end PCPVerifier

/-- For any `(c, 1 / 2)`-PCP verifier of `A` with `c > 1 / 2`, an instance `a` is in `A` if and
only if some table makes `V.majorityTableVerifier` accept. -/
theorem IsPCPVerifierWith.mem_iff_exists_majorityTableVerifier {c : ℝ} {r q : ℕ → ℕ}
    {V : PCPVerifier α} {A : Set α} (hc : 1 / 2 < c)
    (h : IsPCPVerifierWith enc c (1 / 2) r q V A) (a : α) :
    a ∈ A ↔ ∃ table, V.majorityTableVerifier (a, table) = true := by
  refine ⟨fun ha => ?_, fun ⟨table, htable⟩ => ?_⟩
  · obtain ⟨proof, hproof⟩ := h.complete a ha
    exact ⟨_, by simpa using V.majorityTableVerifier_complete a proof [] (hc.trans_le hproof)⟩
  · by_contra ha
    simp only [PCPVerifier.majorityTableVerifier, BitString.length_enumList,
      decide_eq_true_eq, V.tableAcceptCount_eq_acceptCount_proofOfTable] at htable
    have hsound := (V.acceptProb_le_half_iff a (V.proofOfTable a table)).mp
      (h.sound a ha (V.proofOfTable a table))
    omega

/-- Logarithmically many random bits with completeness `c > 1 / 2` and soundness `1 / 2` can be
checked exhaustively in `NP`, regardless of the query bound `q`. -/
theorem PCPWith_log_subset_NP {c : ℝ} (hc : 1 / 2 < c) (q : ℕ → ℕ) :
    PCPWith c (1 / 2) (fun n => Nat.log 2 n + 1) q enc ⊆ NP enc := by
  rintro A ⟨V, c_r, c_q, hV, hpcp⟩
  exact PCPVerifier.mem_NP_of_tableCheck hV hpcp.coins_le
    (V.isPolyTime_majorityTableVerifier hV hpcp.coins_le)
    (fun a ha =>
      let ⟨proof, hproof⟩ := hpcp.complete a ha
      ⟨proof, fun padding => V.majorityTableVerifier_complete a proof padding (hc.trans_le hproof)⟩)
    (fun a table htable => (hpcp.mem_iff_exists_majorityTableVerifier hc a).mpr ⟨table, htable⟩)

/-- For every positive constant `q ≥ 1`, `PCP(log n, q) = NP`. -/
theorem PCP_log_const {q : ℕ} (hq : 1 ≤ q) :
    PCP (fun n => Nat.log 2 n + 1) (fun _ => q) enc = NP enc := by
  refine Set.Subset.antisymm (PCP_log_subset_NP _) ?_
  rw [NP_eq_PCP_log enc]
  exact PCP_mono_queries fun _ => hq

/-- **Arora and Barak, Chapter 18, Problem 2 (corrected):** for every constant `q ≥ 1` and
completeness threshold `1 / 2 < c ≤ 1`,
`PCPWith c (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => q) enc =
  PCP (fun n => Nat.log 2 n + 1) (fun _ => q) enc`. -/
theorem PCPWith_log_const {c : ℝ} {q : ℕ} (hc : 1 / 2 < c) (hc1 : c ≤ 1) (hq : 1 ≤ q) :
    PCPWith c (1 / 2) (fun n => Nat.log 2 n + 1) (fun _ => q) enc =
      PCP (fun n => Nat.log 2 n + 1) (fun _ => q) enc := by
  refine Set.Subset.antisymm ?_ ?_
  · rw [PCP_log_const hq]
    exact PCPWith_log_subset_NP hc _
  · rw [← PCPWith_one_half]
    exact PCPWith_mono_thresholds hc1 le_rfl

end Cslib.Complexity
